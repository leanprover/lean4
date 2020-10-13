// Lean compiler output
// Module: Lean.PrettyPrinter
// Imports: Init Lean.Delaborator Lean.PrettyPrinter.Parenthesizer Lean.PrettyPrinter.Formatter Lean.Parser.Module
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
lean_object* l_Lean_sanitizeSyntax(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_registerPPExt___closed__1;
lean_object* l_Lean_PPContext_runMetaM___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_InternalExceptionId_toString___closed__1;
extern lean_object* l_Lean_Meta_hasEval___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_registerPPExt(lean_object*);
extern lean_object* l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__1;
lean_object* l_Lean_PrettyPrinter_registerPPExt___closed__2;
lean_object* l___private_Lean_Meta_Basic_31__withLocalContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_registerPPExt___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCommand(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Parser_Module_module_formatter___closed__1;
lean_object* l_Lean_PrettyPrinter_parenthesizeTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext___at_Lean_PrettyPrinter_registerPPExt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PPContext_runMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr___closed__1;
lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PPContext_runCoreM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_registerPPExt___closed__3;
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Lean_ppFnsRef;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_PrettyPrinter_ppExpr___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_PrettyPrinter_ppExpr___spec__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_registerPPExt___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PPContext_runCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_PrettyPrinter_3__regTraceClasses(lean_object*);
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext(lean_object*);
lean_object* l_Lean_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext___at_Lean_PrettyPrinter_registerPPExt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PPContext_runCoreM(lean_object*);
lean_object* l___private_Lean_PrettyPrinter_1__noContext___main___boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l___private_Lean_PrettyPrinter_1__noContext___main(lean_object*);
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Unhygienic_run___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_registerPPExt___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PPContext_runMetaM(lean_object*);
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext___rarg___lambda__1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__1;
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l___private_Lean_PrettyPrinter_1__noContext(lean_object*);
lean_object* l___private_Lean_PrettyPrinter_1__noContext___boxed(lean_object*);
extern lean_object* l_Lean_Meta_State_inhabited___closed__6;
lean_object* l_Lean_PPContext_runCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unsigned_to_nat(1000u);
x_8 = lean_box(0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
x_10 = l_Lean_Unhygienic_run___rarg___closed__1;
x_11 = l_Lean_NameGenerator_Inhabited___closed__3;
x_12 = l_Lean_TraceState_Inhabited___closed__1;
lean_inc(x_4);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_st_mk_ref(x_13, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = lean_apply_3(x_2, x_9, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_15);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_MessageData_toString(x_27, x_26);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_17, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = l_Nat_repr(x_42);
x_44 = l_Lean_InternalExceptionId_toString___closed__1;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_17, 0, x_46);
return x_17;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_dec(x_17);
x_48 = lean_ctor_get(x_25, 0);
lean_inc(x_48);
lean_dec(x_25);
x_49 = l_Nat_repr(x_48);
x_50 = l_Lean_InternalExceptionId_toString___closed__1;
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
}
}
}
lean_object* l_Lean_PPContext_runCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PPContext_runCoreM___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PPContext_runCoreM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runCoreM___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_PPContext_runMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Meta_hasEval___rarg___closed__1;
x_6 = l_Array_empty___closed__1;
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_Meta_State_inhabited___closed__6;
x_10 = l_Lean_NameSet_empty;
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run_x27___rarg), 6, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_PPContext_runCoreM___rarg(x_1, x_12, x_3);
return x_13;
}
}
lean_object* l_Lean_PPContext_runMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PPContext_runMetaM___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PPContext_runMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runMetaM___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Lean_sanitizeSyntax(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_PrettyPrinter_parenthesizeTerm(x_9, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_formatTerm(x_11, x_2, x_3, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_withLCtx___at_Lean_PrettyPrinter_ppExpr___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_31__withLocalContextImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Meta_withLCtx___at_Lean_PrettyPrinter_ppExpr___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at_Lean_PrettyPrinter_ppExpr___spec__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_ppExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_ppTerm(x_1, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Lean_LocalContext_sanitizeNames(x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_delab), 9, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_11);
x_16 = l_Lean_PrettyPrinter_ppExpr___closed__1;
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Array_empty___closed__1;
x_19 = l_Lean_Meta_withLCtx___at_Lean_PrettyPrinter_ppExpr___spec__1___rarg(x_14, x_18, x_17, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
}
lean_object* l_Lean_PrettyPrinter_ppExpr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_ppExpr___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___regBuiltin_Lean_Parser_Module_module_parenthesizer___closed__1;
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_PrettyPrinter_parenthesize(x_5, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___regBuiltin_Lean_Parser_Module_module_formatter___closed__1;
x_10 = l_Lean_PrettyPrinter_format(x_9, x_7, x_2, x_3, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_PrettyPrinter_1__noContext___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
x_1 = x_2;
goto _start;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l___private_Lean_PrettyPrinter_1__noContext___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_PrettyPrinter_1__noContext___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_PrettyPrinter_1__noContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_PrettyPrinter_1__noContext___main(x_1);
return x_2;
}
}
lean_object* l___private_Lean_PrettyPrinter_1__noContext___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_PrettyPrinter_1__noContext(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext___rarg___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l___private_Lean_PrettyPrinter_1__noContext___main(x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = l___private_Lean_PrettyPrinter_1__noContext___main(x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
return x_1;
}
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_2__withoutContext___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_2__withoutContext___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_PrettyPrinter_2__withoutContext___rarg___closed__1;
x_4 = lean_apply_3(x_1, lean_box(0), x_3, x_2);
return x_4;
}
}
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_2__withoutContext___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext___at_Lean_PrettyPrinter_registerPPExt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = l___private_Lean_PrettyPrinter_1__noContext___main(x_16);
lean_dec(x_16);
lean_ctor_set(x_12, 1, x_17);
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = l___private_Lean_PrettyPrinter_1__noContext___main(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_25 = x_12;
} else {
 lean_dec_ref(x_12);
 x_25 = lean_box(0);
}
x_26 = l___private_Lean_PrettyPrinter_1__noContext___main(x_24);
lean_dec(x_24);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_7, 0);
lean_dec(x_30);
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_dec(x_7);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l___private_Lean_PrettyPrinter_2__withoutContext___at_Lean_PrettyPrinter_registerPPExt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_5, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = l___private_Lean_PrettyPrinter_1__noContext___main(x_14);
lean_dec(x_14);
lean_ctor_set(x_10, 1, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = l___private_Lean_PrettyPrinter_1__noContext___main(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_23 = x_10;
} else {
 lean_dec_ref(x_10);
 x_23 = lean_box(0);
}
x_24 = l___private_Lean_PrettyPrinter_1__noContext___main(x_22);
lean_dec(x_22);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_5, 0);
lean_dec(x_28);
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_registerPPExt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr), 8, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_2__withoutContext___at_Lean_PrettyPrinter_registerPPExt___spec__1), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_Lean_PPContext_runMetaM___rarg(x_1, x_7, x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_registerPPExt___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTerm), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_2__withoutContext___at_Lean_PrettyPrinter_registerPPExt___spec__2), 4, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Lean_PPContext_runCoreM___rarg(x_1, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerPPExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_registerPPExt___lambda__1), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerPPExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_registerPPExt___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerPPExt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_registerPPExt___closed__1;
x_2 = l_Lean_PrettyPrinter_registerPPExt___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_registerPPExt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_ppFnsRef;
x_3 = l_Lean_PrettyPrinter_registerPPExt___closed__3;
x_4 = lean_st_ref_set(x_2, x_3, x_1);
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
lean_object* l_Lean_PrettyPrinter_registerPPExt___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_registerPPExt___lambda__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_PrettyPrinter_3__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Delaborator(lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Formatter(lean_object*);
lean_object* initialize_Lean_Parser_Module(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_PrettyPrinter(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
res = initialize_Lean_Parser_Module(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_ppExpr___closed__1 = _init_l_Lean_PrettyPrinter_ppExpr___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExpr___closed__1);
l___private_Lean_PrettyPrinter_2__withoutContext___rarg___closed__1 = _init_l___private_Lean_PrettyPrinter_2__withoutContext___rarg___closed__1();
lean_mark_persistent(l___private_Lean_PrettyPrinter_2__withoutContext___rarg___closed__1);
l_Lean_PrettyPrinter_registerPPExt___closed__1 = _init_l_Lean_PrettyPrinter_registerPPExt___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_registerPPExt___closed__1);
l_Lean_PrettyPrinter_registerPPExt___closed__2 = _init_l_Lean_PrettyPrinter_registerPPExt___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_registerPPExt___closed__2);
l_Lean_PrettyPrinter_registerPPExt___closed__3 = _init_l_Lean_PrettyPrinter_registerPPExt___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_registerPPExt___closed__3);
res = l_Lean_PrettyPrinter_registerPPExt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_3__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
