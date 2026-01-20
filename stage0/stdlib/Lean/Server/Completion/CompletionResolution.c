// Lean compiler output
// Module: Lean.Server.Completion.CompletionResolution
// Imports: public import Lean.Data.Lsp public import Lean.Server.Completion.CompletionInfoSelection public import Lean.Linter.Deprecated
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
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Linter_instInhabitedDeprecationEntry_default;
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__5;
lean_object* l_Lean_Server_Completion_findCompletionInfosAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_CompletionInfo_lctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__0(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__1;
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__6;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lean_Linter_deprecatedAttr;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__4;
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__8;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__9;
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_12 = 1;
x_13 = l_Lean_instBEqBinderInfo_beq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, lean_box(0));
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_dec_ref(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
x_16 = 0;
x_17 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(x_8, x_11, x_9, x_15, x_16, x_3, x_4, x_5, x_6);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, lean_box(0));
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_expr_instantiate1(x_1, x_3);
x_10 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(x_9, x_2, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_CompletionItem_resolve___lam__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_ppExpr(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_Format_defWidth;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Std_Format_pretty(x_9, x_10, x_11, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_Std_Format_defWidth;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Std_Format_pretty(x_13, x_14, x_15, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Lsp_CompletionItem_resolve___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(some ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has been deprecated, use `", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` instead.", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has been deprecated.", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_178; lean_object* x_179; 
x_24 = lean_st_ref_get(x_6);
x_25 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_ctor_get(x_1, 4);
x_31 = lean_ctor_get(x_1, 5);
x_32 = lean_ctor_get(x_1, 6);
x_33 = lean_ctor_get(x_1, 7);
x_34 = l_Lean_Lsp_CompletionItem_resolve___closed__0;
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_dec_ref(x_1);
x_182 = l_Lean_Lsp_CompletionItem_resolve___closed__9;
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_191; uint8_t x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_2, 0);
x_192 = 0;
lean_inc(x_191);
lean_inc_ref(x_25);
x_193 = l_Lean_Environment_find_x3f(x_25, x_191, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_178 = x_27;
x_179 = lean_box(0);
goto block_181;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = l_Lean_ConstantInfo_type(x_194);
lean_dec(x_194);
x_183 = x_195;
goto block_190;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_2, 0);
x_197 = lean_ctor_get(x_3, 2);
lean_inc(x_196);
lean_inc_ref(x_197);
x_198 = lean_local_ctx_find(x_197, x_196);
if (lean_obj_tag(x_198) == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_178 = x_27;
x_179 = lean_box(0);
goto block_181;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
x_200 = l_Lean_LocalDecl_type(x_199);
lean_dec(x_199);
x_183 = x_200;
goto block_190;
}
}
block_190:
{
lean_object* x_184; 
lean_inc_ref(x_5);
x_184 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(x_183, x_182, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
x_178 = x_186;
x_179 = lean_box(0);
goto block_181;
}
else
{
uint8_t x_187; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_187 = !lean_is_exclusive(x_184);
if (x_187 == 0)
{
return x_184;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_184, 0);
lean_inc(x_188);
lean_dec(x_184);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_109 = x_1;
x_110 = x_28;
x_111 = x_5;
x_112 = lean_box(0);
goto block_177;
}
block_23:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 2);
lean_dec(x_12);
lean_ctor_set(x_8, 2, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
x_16 = lean_ctor_get(x_8, 3);
x_17 = lean_ctor_get(x_8, 4);
x_18 = lean_ctor_get(x_8, 5);
x_19 = lean_ctor_get(x_8, 6);
x_20 = lean_ctor_get(x_8, 7);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_10);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_17);
lean_ctor_set(x_21, 5, x_18);
lean_ctor_set(x_21, 6, x_19);
lean_ctor_set(x_21, 7, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
block_43:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Lean_Lsp_CompletionItem_resolve___closed__1;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_string_append(x_40, x_35);
lean_dec_ref(x_35);
x_42 = l_Lean_Lsp_CompletionItem_resolve___lam__0(x_41);
x_8 = x_36;
x_9 = lean_box(0);
x_10 = x_42;
goto block_23;
}
block_63:
{
if (lean_obj_tag(x_46) == 0)
{
if (lean_obj_tag(x_48) == 0)
{
lean_dec_ref(x_45);
x_8 = x_47;
x_9 = lean_box(0);
x_10 = x_44;
goto block_23;
}
else
{
lean_object* x_50; 
lean_dec(x_44);
x_50 = lean_apply_1(x_45, x_48);
x_8 = x_47;
x_9 = lean_box(0);
x_10 = x_50;
goto block_23;
}
}
else
{
lean_dec(x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec_ref(x_46);
x_52 = lean_apply_1(x_45, x_51);
x_8 = x_47;
x_9 = lean_box(0);
x_10 = x_52;
goto block_23;
}
else
{
lean_object* x_53; 
lean_dec_ref(x_45);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec_ref(x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec_ref(x_48);
x_55 = l_Lean_Lsp_CompletionItem_resolve___closed__2;
x_35 = x_54;
x_36 = x_47;
x_37 = lean_box(0);
x_38 = x_55;
goto block_43;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec_ref(x_48);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec_ref(x_53);
x_58 = l_Lean_Lsp_CompletionItem_resolve___closed__3;
x_59 = l_addParenHeuristic(x_57);
x_60 = lean_string_append(x_58, x_59);
lean_dec_ref(x_59);
x_61 = l_Lean_Lsp_CompletionItem_resolve___closed__4;
x_62 = lean_string_append(x_60, x_61);
x_35 = x_56;
x_36 = x_47;
x_37 = lean_box(0);
x_38 = x_62;
goto block_43;
}
}
}
}
block_99:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_2);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_2, 0);
x_73 = l_Lean_findDocString_x3f(x_25, x_72, x_66);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
lean_free_object(x_2);
lean_dec_ref(x_67);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_44 = x_65;
x_45 = x_69;
x_46 = x_70;
x_47 = x_64;
x_48 = x_74;
x_49 = lean_box(0);
goto block_63;
}
else
{
uint8_t x_75; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_65);
lean_dec_ref(x_64);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_73, 0);
x_77 = lean_ctor_get(x_67, 5);
lean_inc(x_77);
lean_dec_ref(x_67);
x_78 = lean_io_error_to_string(x_76);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_78);
x_79 = l_Lean_MessageData_ofFormat(x_2);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_73, 0, x_80);
return x_73;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_73, 0);
lean_inc(x_81);
lean_dec(x_73);
x_82 = lean_ctor_get(x_67, 5);
lean_inc(x_82);
lean_dec_ref(x_67);
x_83 = lean_io_error_to_string(x_81);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_83);
x_84 = l_Lean_MessageData_ofFormat(x_2);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_2, 0);
lean_inc(x_87);
lean_dec(x_2);
x_88 = l_Lean_findDocString_x3f(x_25, x_87, x_66);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
lean_dec_ref(x_67);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_44 = x_65;
x_45 = x_69;
x_46 = x_70;
x_47 = x_64;
x_48 = x_89;
x_49 = lean_box(0);
goto block_63;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_65);
lean_dec_ref(x_64);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_67, 5);
lean_inc(x_92);
lean_dec_ref(x_67);
x_93 = lean_io_error_to_string(x_90);
x_94 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l_Lean_MessageData_ofFormat(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
if (lean_is_scalar(x_91)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_91;
}
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec_ref(x_67);
lean_dec_ref(x_25);
lean_dec_ref(x_2);
x_98 = lean_box(0);
x_44 = x_65;
x_45 = x_69;
x_46 = x_70;
x_47 = x_64;
x_48 = x_98;
x_49 = lean_box(0);
goto block_63;
}
}
block_108:
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_64 = x_100;
x_65 = x_101;
x_66 = x_102;
x_67 = x_103;
x_68 = lean_box(0);
x_69 = x_105;
x_70 = x_107;
goto block_99;
}
block_177:
{
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed), 3, 2);
lean_closure_set(x_113, 0, x_110);
lean_closure_set(x_113, 1, x_34);
x_114 = 1;
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_2, 0);
x_116 = l_Lean_Linter_instInhabitedDeprecationEntry_default;
x_117 = l_Lean_Linter_deprecatedAttr;
lean_inc(x_115);
lean_inc_ref(x_25);
x_118 = l_Lean_ParametricAttribute_getParam_x3f___redArg(x_116, x_117, x_25, x_115);
if (lean_obj_tag(x_118) == 1)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_120, 1);
if (lean_obj_tag(x_121) == 1)
{
lean_inc_ref(x_121);
lean_dec(x_120);
lean_ctor_set(x_118, 0, x_121);
x_64 = x_109;
x_65 = x_110;
x_66 = x_114;
x_67 = x_111;
x_68 = lean_box(0);
x_69 = x_113;
x_70 = x_118;
goto block_99;
}
else
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
if (lean_obj_tag(x_122) == 1)
{
uint8_t x_123; 
lean_free_object(x_118);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = l_Lean_Lsp_CompletionItem_resolve___closed__5;
lean_inc(x_115);
x_126 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_115, x_114);
x_127 = lean_string_append(x_125, x_126);
lean_dec_ref(x_126);
x_128 = l_Lean_Lsp_CompletionItem_resolve___closed__6;
x_129 = lean_string_append(x_127, x_128);
x_130 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_124, x_114);
x_131 = lean_string_append(x_129, x_130);
lean_dec_ref(x_130);
x_132 = l_Lean_Lsp_CompletionItem_resolve___closed__7;
x_133 = lean_string_append(x_131, x_132);
lean_ctor_set(x_122, 0, x_133);
x_100 = x_109;
x_101 = x_110;
x_102 = x_114;
x_103 = x_111;
x_104 = lean_box(0);
x_105 = x_113;
x_106 = x_122;
goto block_108;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_134 = lean_ctor_get(x_122, 0);
lean_inc(x_134);
lean_dec(x_122);
x_135 = l_Lean_Lsp_CompletionItem_resolve___closed__5;
lean_inc(x_115);
x_136 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_115, x_114);
x_137 = lean_string_append(x_135, x_136);
lean_dec_ref(x_136);
x_138 = l_Lean_Lsp_CompletionItem_resolve___closed__6;
x_139 = lean_string_append(x_137, x_138);
x_140 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_134, x_114);
x_141 = lean_string_append(x_139, x_140);
lean_dec_ref(x_140);
x_142 = l_Lean_Lsp_CompletionItem_resolve___closed__7;
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_100 = x_109;
x_101 = x_110;
x_102 = x_114;
x_103 = x_111;
x_104 = lean_box(0);
x_105 = x_113;
x_106 = x_144;
goto block_108;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_122);
x_145 = l_Lean_Lsp_CompletionItem_resolve___closed__5;
lean_inc(x_115);
x_146 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_115, x_114);
x_147 = lean_string_append(x_145, x_146);
lean_dec_ref(x_146);
x_148 = l_Lean_Lsp_CompletionItem_resolve___closed__8;
x_149 = lean_string_append(x_147, x_148);
lean_ctor_set(x_118, 0, x_149);
x_100 = x_109;
x_101 = x_110;
x_102 = x_114;
x_103 = x_111;
x_104 = lean_box(0);
x_105 = x_113;
x_106 = x_118;
goto block_108;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_118, 0);
lean_inc(x_150);
lean_dec(x_118);
x_151 = lean_ctor_get(x_150, 1);
if (lean_obj_tag(x_151) == 1)
{
lean_object* x_152; 
lean_inc_ref(x_151);
lean_dec(x_150);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_64 = x_109;
x_65 = x_110;
x_66 = x_114;
x_67 = x_111;
x_68 = lean_box(0);
x_69 = x_113;
x_70 = x_152;
goto block_99;
}
else
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
lean_dec(x_150);
if (lean_obj_tag(x_153) == 1)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
x_156 = l_Lean_Lsp_CompletionItem_resolve___closed__5;
lean_inc(x_115);
x_157 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_115, x_114);
x_158 = lean_string_append(x_156, x_157);
lean_dec_ref(x_157);
x_159 = l_Lean_Lsp_CompletionItem_resolve___closed__6;
x_160 = lean_string_append(x_158, x_159);
x_161 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_154, x_114);
x_162 = lean_string_append(x_160, x_161);
lean_dec_ref(x_161);
x_163 = l_Lean_Lsp_CompletionItem_resolve___closed__7;
x_164 = lean_string_append(x_162, x_163);
if (lean_is_scalar(x_155)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_155;
}
lean_ctor_set(x_165, 0, x_164);
x_100 = x_109;
x_101 = x_110;
x_102 = x_114;
x_103 = x_111;
x_104 = lean_box(0);
x_105 = x_113;
x_106 = x_165;
goto block_108;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_153);
x_166 = l_Lean_Lsp_CompletionItem_resolve___closed__5;
lean_inc(x_115);
x_167 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_115, x_114);
x_168 = lean_string_append(x_166, x_167);
lean_dec_ref(x_167);
x_169 = l_Lean_Lsp_CompletionItem_resolve___closed__8;
x_170 = lean_string_append(x_168, x_169);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_100 = x_109;
x_101 = x_110;
x_102 = x_114;
x_103 = x_111;
x_104 = lean_box(0);
x_105 = x_113;
x_106 = x_171;
goto block_108;
}
}
}
}
else
{
lean_object* x_172; 
lean_dec(x_118);
x_172 = lean_box(0);
x_64 = x_109;
x_65 = x_110;
x_66 = x_114;
x_67 = x_111;
x_68 = lean_box(0);
x_69 = x_113;
x_70 = x_172;
goto block_99;
}
}
else
{
lean_object* x_173; 
x_173 = lean_box(0);
x_64 = x_109;
x_65 = x_110;
x_66 = x_114;
x_67 = x_111;
x_68 = lean_box(0);
x_69 = x_113;
x_70 = x_173;
goto block_99;
}
}
else
{
uint8_t x_174; 
lean_dec_ref(x_111);
lean_dec_ref(x_25);
lean_dec_ref(x_2);
x_174 = !lean_is_exclusive(x_110);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_110, 0);
lean_dec(x_175);
lean_ctor_set_tag(x_110, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
else
{
lean_object* x_176; 
lean_dec(x_110);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_109);
return x_176;
}
}
}
block_181:
{
lean_object* x_180; 
lean_inc(x_28);
x_180 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_180, 0, x_26);
lean_ctor_set(x_180, 1, x_178);
lean_ctor_set(x_180, 2, x_28);
lean_ctor_set(x_180, 3, x_29);
lean_ctor_set(x_180, 4, x_30);
lean_ctor_set(x_180, 5, x_31);
lean_ctor_set(x_180, 6, x_32);
lean_ctor_set(x_180, 7, x_33);
x_109 = x_180;
x_110 = x_28;
x_111 = x_5;
x_112 = lean_box(0);
goto block_177;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Lsp_CompletionItem_resolve(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_Lean_Server_Completion_findCompletionInfosAt(x_1, x_2, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_nat_dec_lt(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_fget(x_10, x_7);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_CompletionInfo_lctx(x_16);
lean_dec_ref(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___boxed), 7, 2);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_6);
x_19 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_15, x_17, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_Completion_resolveCompletionItem_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_9;
}
}
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin);
lean_object* initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_CompletionItem_resolve___closed__0 = _init_l_Lean_Lsp_CompletionItem_resolve___closed__0();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_resolve___closed__0);
l_Lean_Lsp_CompletionItem_resolve___closed__1 = _init_l_Lean_Lsp_CompletionItem_resolve___closed__1();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_resolve___closed__1);
l_Lean_Lsp_CompletionItem_resolve___closed__2 = _init_l_Lean_Lsp_CompletionItem_resolve___closed__2();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_resolve___closed__2);
l_Lean_Lsp_CompletionItem_resolve___closed__3 = _init_l_Lean_Lsp_CompletionItem_resolve___closed__3();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_resolve___closed__3);
l_Lean_Lsp_CompletionItem_resolve___closed__4 = _init_l_Lean_Lsp_CompletionItem_resolve___closed__4();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_resolve___closed__4);
l_Lean_Lsp_CompletionItem_resolve___closed__5 = _init_l_Lean_Lsp_CompletionItem_resolve___closed__5();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_resolve___closed__5);
l_Lean_Lsp_CompletionItem_resolve___closed__6 = _init_l_Lean_Lsp_CompletionItem_resolve___closed__6();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_resolve___closed__6);
l_Lean_Lsp_CompletionItem_resolve___closed__7 = _init_l_Lean_Lsp_CompletionItem_resolve___closed__7();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_resolve___closed__7);
l_Lean_Lsp_CompletionItem_resolve___closed__8 = _init_l_Lean_Lsp_CompletionItem_resolve___closed__8();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_resolve___closed__8);
l_Lean_Lsp_CompletionItem_resolve___closed__9 = _init_l_Lean_Lsp_CompletionItem_resolve___closed__9();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_resolve___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
