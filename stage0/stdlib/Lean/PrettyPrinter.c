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
lean_object* l_Std_PersistentArray_forM___at_Lean_Core_CoreM_run_x27___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__3;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__2;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getEnv___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_reprint___main(lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_MessageData_formatAux___main(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__1;
extern lean_object* l_Lean_ppExprFnRef;
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_MetaM_toECoreM___rarg___closed__3;
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_PrettyPrinter_ppExprFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxRecDepth(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4;
lean_object* l_Lean_PrettyPrinter_registerPPTerm(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__1;
lean_object* l_Lean_Core_getRef___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
extern lean_object* l_Lean_Meta_MetaM_toECoreM___rarg___closed__1;
lean_object* l_Lean_Meta_setMCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_getTraceState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2;
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_PrettyPrinter_parenthesizeTerm(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PrettyPrinter_formatTerm(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_delab(x_2, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_ppTerm(x_1, x_10, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_PrettyPrinter_parenthesizeCommand(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PrettyPrinter_formatCommand(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
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
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_17 = l_Lean_PrettyPrinter_ppCommand(x_1, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
x_21 = l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___closed__2;
x_22 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_20);
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_20);
x_4 = x_16;
x_5 = x_23;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = l_Lean_Syntax_reprint___main(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_11 = l_Lean_Meta_isClassQuick___main___closed__1;
x_12 = l_unreachable_x21___rarg(x_11);
x_13 = lean_apply_5(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Syntax_getArgs(x_2);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Array_extract___rarg(x_15, x_17, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1(x_1, x_2, x_18, x_8, x_19, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_18);
return x_20;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___main___at_Lean_PrettyPrinter_ppModule___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_PrettyPrinter_ppModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_ppModule(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
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
lean_object* l_Lean_PrettyPrinter_ppExprFnUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_18; lean_object* x_24; lean_object* x_25; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_45 = l_Lean_getMaxRecDepth(x_5);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_47);
x_49 = l_Lean_NameGenerator_Inhabited___closed__3;
x_50 = l_Lean_TraceState_Inhabited___closed__1;
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_box(0);
x_53 = lean_io_mk_ref(x_51, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_84 = l_Lean_Core_getRef___rarg(x_48, x_54, x_55);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_MetaM_toECoreM___rarg___closed__3;
x_88 = lean_io_mk_ref(x_87, x_86);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Meta_MetaM_toECoreM___rarg___closed__1;
x_92 = l_Array_empty___closed__1;
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_4);
lean_ctor_set(x_93, 2, x_92);
x_94 = l_Lean_Meta_setMCtx(x_3, x_93, x_89, x_48, x_54, x_90);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
lean_inc(x_54);
lean_inc(x_48);
lean_inc(x_89);
x_96 = l_Lean_PrettyPrinter_ppExpr(x_1, x_6, x_93, x_89, x_48, x_54, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_85);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_io_ref_get(x_89, x_98);
lean_dec(x_89);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l_Lean_Core_getEnv___rarg(x_54, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_97);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_56 = x_105;
x_57 = x_103;
goto block_83;
}
else
{
lean_object* x_106; 
lean_dec(x_89);
x_106 = lean_ctor_get(x_96, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 2)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_85);
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
lean_dec(x_96);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_56 = x_109;
x_57 = x_107;
goto block_83;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_96, 1);
lean_inc(x_110);
lean_dec(x_96);
x_111 = l_Lean_Meta_Exception_toMessageData(x_106);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_85);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_56 = x_113;
x_57 = x_110;
goto block_83;
}
}
block_17:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_io_error_to_string(x_8);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 0;
x_12 = l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2;
x_13 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_11);
x_14 = l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4;
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_11);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
return x_16;
}
}
block_23:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_7 = x_20;
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_7 = x_22;
goto block_17;
}
}
block_44:
{
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_18 = x_27;
goto block_23;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l_Lean_KernelException_toMessageData(x_28, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_MessageData_formatAux___main(x_31, x_30);
x_33 = l_Lean_Options_empty;
x_34 = l_Lean_Format_pretty(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_25);
x_18 = x_36;
goto block_23;
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_box(0);
x_39 = l_Lean_MessageData_formatAux___main(x_38, x_37);
x_40 = l_Lean_Options_empty;
x_41 = l_Lean_Format_pretty(x_39, x_40);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_25);
x_18 = x_43;
goto block_23;
}
}
}
block_83:
{
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Core_getTraceState___rarg(x_54, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Std_PersistentArray_forM___at_Lean_Core_CoreM_run_x27___spec__3(x_62, x_48, x_54, x_61);
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_24 = x_58;
x_25 = x_64;
goto block_44;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_58);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_24 = x_65;
x_25 = x_66;
goto block_44;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
x_68 = l_Lean_Core_getTraceState___rarg(x_54, x_57);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Std_PersistentArray_forM___at_Lean_Core_CoreM_run_x27___spec__3(x_71, x_48, x_54, x_70);
lean_dec(x_48);
lean_dec(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_io_ref_get(x_54, x_73);
lean_dec(x_54);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_dec(x_67);
lean_ctor_set(x_74, 0, x_77);
x_18 = x_74;
goto block_23;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_dec(x_67);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_18 = x_80;
goto block_23;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_67);
lean_dec(x_54);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_72, 1);
lean_inc(x_82);
lean_dec(x_72);
x_24 = x_81;
x_25 = x_82;
goto block_44;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_ppExprFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_ppExprFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_ppExprFn(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_registerPPTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = l_Lean_Parser_builtinTokenTable;
x_3 = lean_io_ref_get(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprFnUnsafe), 6, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = l_Lean_ppExprFnRef;
x_8 = lean_io_ref_set(x_7, x_6, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
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
l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__1 = _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__1);
l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2 = _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__2);
l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__3 = _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__3);
l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4 = _init_l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprFnUnsafe___closed__4);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
