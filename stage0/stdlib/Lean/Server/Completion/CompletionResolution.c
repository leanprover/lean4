// Lean compiler output
// Module: Lean.Server.Completion.CompletionResolution
// Imports: Lean.Server.Completion.CompletionItemData Lean.Server.Completion.CompletionInfoSelection Lean.Linter.Deprecated
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
static lean_object* l_Lean_Lsp_instToJsonResolvableCompletionItemData___closed__0;
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_416__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__17____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__8____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* l_Lean_Lsp_toJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_416_;
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Lsp_fromJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2972_(lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__11____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* l_Lean_Lsp_instFromJsonCompletionIdentifier___closed__0;
static lean_object* l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2_spec__2___closed__0;
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at___Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_416__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__19____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__5;
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__13____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_411_(uint8_t, uint8_t);
lean_object* l_Lean_Server_Completion_findCompletionInfosAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___Array_appendList_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedDeprecationEntry;
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__22____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__15____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_29_(lean_object*);
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
lean_object* l_Lean_Elab_CompletionInfo_lctx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonResolvableCompletionItemData;
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__9____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionIdentifier;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__7;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29____boxed(lean_object*);
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
LEAN_EXPORT lean_object* l_Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_416_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__18____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_object* l_Except_orElseLazy___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__1;
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__6;
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lean_Linter_deprecatedAttr;
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
lean_object* l_Lean_Json_parseTagged(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_toJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_163_(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instFromJsonResolvableCompletionItemData___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__21____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__4;
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__3;
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__10____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__16____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonResolvableCompletionItemData;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__8;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Lsp_instToJsonCompletionIdentifier___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__20____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCompletionIdentifier;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_resolve___closed__2;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__14____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_object* l_Lean_Lsp_toJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_3078_(lean_object*);
static lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
static lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__12____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no inductive constructor matched", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("const", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_7 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_8 = lean_mk_empty_array_with_capacity(x_1);
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Json_parseTagged(x_2, x_6, x_1, x_10);
lean_dec_ref(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Except_orElseLazy___redArg(x_11, x_3);
lean_dec_ref(x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Except_orElseLazy___redArg(x_15, x_3);
lean_dec_ref(x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec_ref(x_11);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_4, x_17, x_18);
lean_dec(x_17);
x_20 = l_Lean_Name_fromJson_x3f(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Except_orElseLazy___redArg(x_20, x_3);
lean_dec_ref(x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Except_orElseLazy___redArg(x_24, x_3);
lean_dec_ref(x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_20, 0, x_28);
x_29 = l_Except_orElseLazy___redArg(x_20, x_3);
lean_dec_ref(x_20);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Except_orElseLazy___redArg(x_32, x_3);
lean_dec_ref(x_32);
return x_33;
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fvar", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("id", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_2 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_29_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_29_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29____boxed), 1, 0);
x_3 = lean_box(0);
x_4 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_5 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29____boxed), 5, 4);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_8 = l_Lean_Json_parseTagged(x_1, x_4, x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Except_orElseLazy___redArg(x_8, x_6);
lean_dec_ref(x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Except_orElseLazy___redArg(x_12, x_6);
lean_dec_ref(x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec_ref(x_8);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_3, x_14, x_15);
lean_dec(x_14);
x_17 = l_Lean_Name_fromJson_x3f(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Except_orElseLazy___redArg(x_17, x_6);
lean_dec_ref(x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Except_orElseLazy___redArg(x_21, x_6);
lean_dec_ref(x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_17, 0, x_25);
x_26 = l_Except_orElseLazy___redArg(x_17, x_6);
lean_dec_ref(x_17);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Except_orElseLazy___redArg(x_29, x_6);
lean_dec_ref(x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionIdentifier___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_fromJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_29_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionIdentifier() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonCompletionIdentifier___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_toJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_163_(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_5 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_6 = 1;
x_7 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_3, x_6);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Json_mkObj(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
x_14 = l_Lean_Json_mkObj(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_17 = l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_18 = 1;
x_19 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_15, x_18);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Json_mkObj(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_Lean_Json_mkObj(x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_31 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_32 = 1;
x_33 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_29, x_32);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Json_mkObj(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
x_40 = l_Lean_Json_mkObj(x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_43 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_44 = 1;
x_45 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_41, x_44);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Json_mkObj(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
x_53 = l_Lean_Json_mkObj(x_52);
return x_53;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonCompletionIdentifier___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_toJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_163_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonCompletionIdentifier() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonCompletionIdentifier___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Lsp_fromJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2972_(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getNat_x3f(x_3);
return x_4;
}
}
static lean_object* _init_l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2_spec__2___closed__0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_fromJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_29_(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2_spec__2(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("params", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lsp", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ResolvableCompletionItemData", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__8____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__9____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__8____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__10____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__9____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__11____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__12____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__11____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__10____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__13____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cPos", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__14____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__13____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__15____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__14____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__16____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__15____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__17____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__11____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__16____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__18____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("id\?", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__19____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__18____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__20____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__19____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__21____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__20____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__22____x40_Lean_Server_Completion_CompletionResolution___hyg_271_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__11____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__21____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_inc(x_1);
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__12____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__12____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__13____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
lean_inc(x_1);
x_17 = l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__1(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__17____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__17____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_ctor_set_tag(x_17, 0);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec_ref(x_17);
x_30 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_31 = l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2(x_1, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_29);
lean_dec(x_15);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__22____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__22____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_40; 
lean_dec(x_29);
lean_dec(x_15);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_ctor_set_tag(x_31, 0);
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_31, 0, x_45);
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_31, 0);
lean_inc(x_46);
lean_dec(x_31);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_29);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__1(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolvableCompletionItemData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonResolvableCompletionItemData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonResolvableCompletionItemData___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_416__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Lsp_toJsonCompletionIdentifier____x40_Lean_Server_Completion_CompletionResolution___hyg_163_(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at___Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_416__spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___Array_appendList_spec__0(lean_box(0), x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Lsp_toJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_416_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_416_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_6 = l_Lean_Lsp_toJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_3078_(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__13____x40_Lean_Server_Completion_CompletionResolution___hyg_271_;
x_11 = l_Lean_JsonNumber_fromNat(x_3);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = l_Lean_Lsp_fromJsonCompletionIdentifier___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_;
x_16 = l_Lean_Json_opt___at___Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_416__spec__0(x_15, x_4);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Lsp_toJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_416_;
x_22 = l_List_flatMapTR_go___at___Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_416__spec__1(x_20, x_21);
x_23 = l_Lean_Json_mkObj(x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonResolvableCompletionItemData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_416_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonResolvableCompletionItemData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonResolvableCompletionItemData___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_expr_instantiate1(x_1, x_3);
x_10 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(x_9, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_12 = 1;
x_13 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_411_(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_14 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
lean_dec_ref(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
x_16 = 0;
x_17 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(x_8, x_11, x_9, x_15, x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_apply_6(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at_____private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_ppExpr(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unsigned_to_nat(120u);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_format_pretty(x_9, x_10, x_11, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_unsigned_to_nat(120u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_format_pretty(x_13, x_15, x_16, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(some ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Linter_deprecatedAttr;
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
x_1 = lean_mk_string_unchecked("` has been deprecated.", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has been deprecated, use `", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_resolve___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` instead.", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_156; lean_object* x_157; 
x_24 = lean_st_ref_get(x_6, x_7);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 7);
lean_inc(x_36);
x_37 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__0), 1, 0);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_1);
x_160 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed), 6, 0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_2, 0);
lean_inc(x_171);
x_172 = 0;
lean_inc_ref(x_28);
x_173 = l_Lean_Environment_find_x3f(x_28, x_171, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_dec_ref(x_160);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_156 = x_30;
x_157 = x_26;
goto block_159;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
x_175 = l_Lean_ConstantInfo_type(x_174);
lean_dec(x_174);
x_161 = x_175;
goto block_170;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_2, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_177);
x_178 = lean_local_ctx_find(x_177, x_176);
if (lean_obj_tag(x_178) == 0)
{
lean_dec_ref(x_160);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_156 = x_30;
x_157 = x_26;
goto block_159;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = lean_ctor_get(x_179, 3);
lean_inc_ref(x_180);
lean_dec(x_179);
x_161 = x_180;
goto block_170;
}
}
block_170:
{
lean_object* x_162; 
lean_inc_ref(x_5);
x_162 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(x_161, x_160, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec_ref(x_162);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_163);
x_156 = x_165;
x_157 = x_164;
goto block_159;
}
else
{
uint8_t x_166; 
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_166 = !lean_is_exclusive(x_162);
if (x_166 == 0)
{
return x_162;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_162, 0);
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_162);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_89 = x_1;
x_90 = x_31;
x_91 = x_5;
x_92 = x_26;
goto block_155;
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
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
}
block_46:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = l_Lean_Lsp_CompletionItem_resolve___closed__0;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_string_append(x_43, x_40);
lean_dec_ref(x_40);
x_45 = l_Lean_Lsp_CompletionItem_resolve___lam__0(x_44);
x_8 = x_38;
x_9 = x_39;
x_10 = x_45;
goto block_23;
}
block_66:
{
if (lean_obj_tag(x_49) == 0)
{
if (lean_obj_tag(x_51) == 0)
{
lean_dec_ref(x_47);
x_8 = x_50;
x_9 = x_52;
x_10 = x_48;
goto block_23;
}
else
{
lean_object* x_53; 
lean_dec(x_48);
x_53 = lean_apply_1(x_47, x_51);
x_8 = x_50;
x_9 = x_52;
x_10 = x_53;
goto block_23;
}
}
else
{
lean_dec(x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
lean_dec_ref(x_49);
x_55 = lean_apply_1(x_47, x_54);
x_8 = x_50;
x_9 = x_52;
x_10 = x_55;
goto block_23;
}
else
{
lean_object* x_56; 
lean_dec_ref(x_47);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec_ref(x_49);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec_ref(x_51);
x_58 = l_Lean_Lsp_CompletionItem_resolve___closed__1;
x_38 = x_50;
x_39 = x_52;
x_40 = x_57;
x_41 = x_58;
goto block_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_51, 0);
lean_inc(x_59);
lean_dec_ref(x_51);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
lean_dec_ref(x_56);
x_61 = l_Lean_Lsp_CompletionItem_resolve___closed__2;
x_62 = l_addParenHeuristic(x_60);
lean_dec(x_60);
x_63 = lean_string_append(x_61, x_62);
lean_dec_ref(x_62);
x_64 = l_Lean_Lsp_CompletionItem_resolve___closed__3;
x_65 = lean_string_append(x_63, x_64);
x_38 = x_50;
x_39 = x_52;
x_40 = x_59;
x_41 = x_65;
goto block_46;
}
}
}
}
block_79:
{
lean_dec_ref(x_67);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
lean_dec_ref(x_2);
x_75 = l_Lean_findDocString_x3f(x_28, x_74, x_72, x_70);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_47 = x_69;
x_48 = x_71;
x_49 = x_73;
x_50 = x_68;
x_51 = x_76;
x_52 = x_77;
goto block_66;
}
else
{
lean_object* x_78; 
lean_dec_ref(x_28);
lean_dec_ref(x_2);
x_78 = lean_box(0);
x_47 = x_69;
x_48 = x_71;
x_49 = x_73;
x_50 = x_68;
x_51 = x_78;
x_52 = x_70;
goto block_66;
}
}
block_88:
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_67 = x_80;
x_68 = x_81;
x_69 = x_82;
x_70 = x_83;
x_71 = x_84;
x_72 = x_85;
x_73 = x_87;
goto block_79;
}
block_155:
{
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_93; uint8_t x_94; 
lean_dec(x_27);
x_93 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed), 3, 2);
lean_closure_set(x_93, 0, x_90);
lean_closure_set(x_93, 1, x_37);
x_94 = 1;
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_2, 0);
lean_inc(x_95);
x_96 = l_Lean_Linter_instInhabitedDeprecationEntry;
x_97 = l_Lean_Lsp_CompletionItem_resolve___closed__4;
lean_inc(x_95);
lean_inc_ref(x_28);
x_98 = l_Lean_ParametricAttribute_getParam_x3f___redArg(x_96, x_97, x_28, x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
lean_dec(x_95);
x_99 = lean_box(0);
x_67 = x_91;
x_68 = x_89;
x_69 = x_93;
x_70 = x_92;
x_71 = x_90;
x_72 = x_94;
x_73 = x_99;
goto block_79;
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = l_Lean_Lsp_CompletionItem_resolve___closed__5;
x_105 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_95, x_94);
x_106 = lean_string_append(x_104, x_105);
lean_dec_ref(x_105);
x_107 = l_Lean_Lsp_CompletionItem_resolve___closed__6;
x_108 = lean_string_append(x_106, x_107);
lean_ctor_set(x_98, 0, x_108);
x_80 = x_91;
x_81 = x_89;
x_82 = x_93;
x_83 = x_92;
x_84 = x_90;
x_85 = x_94;
x_86 = x_98;
goto block_88;
}
else
{
uint8_t x_109; 
lean_free_object(x_98);
x_109 = !lean_is_exclusive(x_103);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_110 = lean_ctor_get(x_103, 0);
x_111 = l_Lean_Lsp_CompletionItem_resolve___closed__5;
x_112 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_95, x_94);
x_113 = lean_string_append(x_111, x_112);
lean_dec_ref(x_112);
x_114 = l_Lean_Lsp_CompletionItem_resolve___closed__7;
x_115 = lean_string_append(x_113, x_114);
x_116 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_110, x_94);
x_117 = lean_string_append(x_115, x_116);
lean_dec_ref(x_116);
x_118 = l_Lean_Lsp_CompletionItem_resolve___closed__8;
x_119 = lean_string_append(x_117, x_118);
lean_ctor_set(x_103, 0, x_119);
x_80 = x_91;
x_81 = x_89;
x_82 = x_93;
x_83 = x_92;
x_84 = x_90;
x_85 = x_94;
x_86 = x_103;
goto block_88;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_120 = lean_ctor_get(x_103, 0);
lean_inc(x_120);
lean_dec(x_103);
x_121 = l_Lean_Lsp_CompletionItem_resolve___closed__5;
x_122 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_95, x_94);
x_123 = lean_string_append(x_121, x_122);
lean_dec_ref(x_122);
x_124 = l_Lean_Lsp_CompletionItem_resolve___closed__7;
x_125 = lean_string_append(x_123, x_124);
x_126 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_120, x_94);
x_127 = lean_string_append(x_125, x_126);
lean_dec_ref(x_126);
x_128 = l_Lean_Lsp_CompletionItem_resolve___closed__8;
x_129 = lean_string_append(x_127, x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_80 = x_91;
x_81 = x_89;
x_82 = x_93;
x_83 = x_92;
x_84 = x_90;
x_85 = x_94;
x_86 = x_130;
goto block_88;
}
}
}
else
{
lean_dec(x_101);
lean_dec(x_95);
lean_ctor_set(x_98, 0, x_102);
x_67 = x_91;
x_68 = x_89;
x_69 = x_93;
x_70 = x_92;
x_71 = x_90;
x_72 = x_94;
x_73 = x_98;
goto block_79;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_98, 0);
lean_inc(x_131);
lean_dec(x_98);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = l_Lean_Lsp_CompletionItem_resolve___closed__5;
x_135 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_95, x_94);
x_136 = lean_string_append(x_134, x_135);
lean_dec_ref(x_135);
x_137 = l_Lean_Lsp_CompletionItem_resolve___closed__6;
x_138 = lean_string_append(x_136, x_137);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_80 = x_91;
x_81 = x_89;
x_82 = x_93;
x_83 = x_92;
x_84 = x_90;
x_85 = x_94;
x_86 = x_139;
goto block_88;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_140 = lean_ctor_get(x_133, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_141 = x_133;
} else {
 lean_dec_ref(x_133);
 x_141 = lean_box(0);
}
x_142 = l_Lean_Lsp_CompletionItem_resolve___closed__5;
x_143 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_95, x_94);
x_144 = lean_string_append(x_142, x_143);
lean_dec_ref(x_143);
x_145 = l_Lean_Lsp_CompletionItem_resolve___closed__7;
x_146 = lean_string_append(x_144, x_145);
x_147 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_140, x_94);
x_148 = lean_string_append(x_146, x_147);
lean_dec_ref(x_147);
x_149 = l_Lean_Lsp_CompletionItem_resolve___closed__8;
x_150 = lean_string_append(x_148, x_149);
if (lean_is_scalar(x_141)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_141;
}
lean_ctor_set(x_151, 0, x_150);
x_80 = x_91;
x_81 = x_89;
x_82 = x_93;
x_83 = x_92;
x_84 = x_90;
x_85 = x_94;
x_86 = x_151;
goto block_88;
}
}
else
{
lean_object* x_152; 
lean_dec(x_131);
lean_dec(x_95);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_132);
x_67 = x_91;
x_68 = x_89;
x_69 = x_93;
x_70 = x_92;
x_71 = x_90;
x_72 = x_94;
x_73 = x_152;
goto block_79;
}
}
}
}
else
{
lean_object* x_153; 
x_153 = lean_box(0);
x_67 = x_91;
x_68 = x_89;
x_69 = x_93;
x_70 = x_92;
x_71 = x_90;
x_72 = x_94;
x_73 = x_153;
goto block_79;
}
}
else
{
lean_object* x_154; 
lean_dec_ref(x_91);
lean_dec_ref(x_90);
lean_dec_ref(x_37);
lean_dec_ref(x_28);
lean_dec_ref(x_2);
if (lean_is_scalar(x_27)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_27;
}
lean_ctor_set(x_154, 0, x_89);
lean_ctor_set(x_154, 1, x_92);
return x_154;
}
}
block_159:
{
lean_object* x_158; 
lean_inc(x_31);
x_158 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_158, 0, x_29);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set(x_158, 2, x_31);
lean_ctor_set(x_158, 3, x_32);
lean_ctor_set(x_158, 4, x_33);
lean_ctor_set(x_158, 5, x_34);
lean_ctor_set(x_158, 6, x_35);
lean_ctor_set(x_158, 7, x_36);
x_89 = x_158;
x_90 = x_31;
x_91 = x_5;
x_92 = x_157;
goto block_155;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Lsp_CompletionItem_resolve___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Server_Completion_findCompletionInfosAt(x_1, x_2, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_7, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_9);
x_15 = lean_array_fget(x_11, x_7);
lean_dec(x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_Elab_CompletionInfo_lctx(x_17);
lean_dec_ref(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve), 7, 2);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_6);
x_20 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_16, x_18, x_19, x_8);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_array_get_size(x_21);
x_23 = lean_nat_dec_lt(x_7, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec_ref(x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_array_fget(x_21, x_7);
lean_dec(x_21);
x_26 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_27);
lean_dec_ref(x_25);
x_28 = l_Lean_Elab_CompletionInfo_lctx(x_27);
lean_dec_ref(x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_resolve), 7, 2);
lean_closure_set(x_29, 0, x_5);
lean_closure_set(x_29, 1, x_6);
x_30 = l_Lean_Elab_ContextInfo_runMetaM___redArg(x_26, x_28, x_29, x_8);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_Completion_resolveCompletionItem_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
lean_object* initialize_Lean_Server_Completion_CompletionItemData(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Completion_CompletionItemData(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___lam__0___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___lam__1___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_fromJsonCompletionIdentifier___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_fromJsonCompletionIdentifier___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_fromJsonCompletionIdentifier___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_fromJsonCompletionIdentifier___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_fromJsonCompletionIdentifier___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_fromJsonCompletionIdentifier___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_29_ = _init_l_Lean_Lsp_fromJsonCompletionIdentifier___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_29_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionIdentifier___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_29_);
l_Lean_Lsp_instFromJsonCompletionIdentifier___closed__0 = _init_l_Lean_Lsp_instFromJsonCompletionIdentifier___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFromJsonCompletionIdentifier___closed__0);
l_Lean_Lsp_instFromJsonCompletionIdentifier = _init_l_Lean_Lsp_instFromJsonCompletionIdentifier();
lean_mark_persistent(l_Lean_Lsp_instFromJsonCompletionIdentifier);
l_Lean_Lsp_instToJsonCompletionIdentifier___closed__0 = _init_l_Lean_Lsp_instToJsonCompletionIdentifier___closed__0();
lean_mark_persistent(l_Lean_Lsp_instToJsonCompletionIdentifier___closed__0);
l_Lean_Lsp_instToJsonCompletionIdentifier = _init_l_Lean_Lsp_instToJsonCompletionIdentifier();
lean_mark_persistent(l_Lean_Lsp_instToJsonCompletionIdentifier);
l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2_spec__2___closed__0 = _init_l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2_spec__2___closed__0();
lean_mark_persistent(l_Option_fromJson_x3f___at___Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_271__spec__2_spec__2___closed__0);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__8____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__8____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__8____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__9____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__9____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__9____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__10____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__10____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__10____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__11____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__11____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__11____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__12____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__12____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__12____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__13____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__13____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__13____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__14____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__14____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__14____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__15____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__15____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__15____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__16____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__16____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__16____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__17____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__17____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__17____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__18____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__18____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__18____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__19____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__19____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__19____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__20____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__20____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__20____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__21____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__21____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__21____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__22____x40_Lean_Server_Completion_CompletionResolution___hyg_271_ = _init_l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__22____x40_Lean_Server_Completion_CompletionResolution___hyg_271_();
lean_mark_persistent(l_Lean_Lsp_fromJsonResolvableCompletionItemData___closed__22____x40_Lean_Server_Completion_CompletionResolution___hyg_271_);
l_Lean_Lsp_instFromJsonResolvableCompletionItemData___closed__0 = _init_l_Lean_Lsp_instFromJsonResolvableCompletionItemData___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFromJsonResolvableCompletionItemData___closed__0);
l_Lean_Lsp_instFromJsonResolvableCompletionItemData = _init_l_Lean_Lsp_instFromJsonResolvableCompletionItemData();
lean_mark_persistent(l_Lean_Lsp_instFromJsonResolvableCompletionItemData);
l_Lean_Lsp_toJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_416_ = _init_l_Lean_Lsp_toJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_416_();
lean_mark_persistent(l_Lean_Lsp_toJsonResolvableCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionResolution___hyg_416_);
l_Lean_Lsp_instToJsonResolvableCompletionItemData___closed__0 = _init_l_Lean_Lsp_instToJsonResolvableCompletionItemData___closed__0();
lean_mark_persistent(l_Lean_Lsp_instToJsonResolvableCompletionItemData___closed__0);
l_Lean_Lsp_instToJsonResolvableCompletionItemData = _init_l_Lean_Lsp_instToJsonResolvableCompletionItemData();
lean_mark_persistent(l_Lean_Lsp_instToJsonResolvableCompletionItemData);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
