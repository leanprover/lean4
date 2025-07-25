// Lean compiler output
// Module: Lean.Server.Completion.CompletionItemData
// Imports: Lean.Server.FileSource
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
static lean_object* l_Lean_Lsp_fromJsonCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_20_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFileSourceCompletionItem;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_20__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___at___Array_appendList_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0;
LEAN_EXPORT uint8_t l_Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_(lean_object*);
static lean_object* l_Lean_Lsp_fromJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0;
static lean_object* l_Lean_Lsp_toJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_87_;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_Lsp_fromJsonCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
static lean_object* l_Lean_Lsp_fromJsonCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
lean_object* l_Lean_Lsp_fromJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2982_(lean_object*);
static lean_object* l_Lean_Lsp_instToJsonCompletionItemData___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20____boxed(lean_object*);
static lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1;
static lean_object* l_Lean_Lsp_instFromJsonCompletionItemData___closed__0;
lean_object* l_Lean_Lsp_toJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_3088_(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionItemData;
static lean_object* l_Lean_Lsp_fromJsonCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21(lean_object*);
static lean_object* l_Lean_Lsp_instFileSourceCompletionItem___closed__0;
static lean_object* l_Lean_Lsp_fromJsonCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCompletionItemData;
static lean_object* l_Lean_Lsp_fromJsonCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_87_(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at___Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_87__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_20__spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_fromJsonCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_20__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Lsp_fromJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2982_(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("params", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionItemData___hyg_20_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionItemData___hyg_20_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lsp", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionItemData___hyg_20_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CompletionItemData", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionItemData___hyg_20_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Lsp_fromJsonCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_2 = l_Lean_Lsp_fromJsonCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_3 = l_Lean_Lsp_fromJsonCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionItemData___hyg_20_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionItemData___hyg_20_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_fromJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionItemData___hyg_20_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_20_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_fromJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_20__spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20____boxed), 1, 0);
x_7 = l_Lean_Lsp_fromJsonCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_8 = 1;
lean_inc_ref(x_6);
x_9 = l_Lean_Name_toString(x_7, x_8, x_6);
x_10 = l_Lean_Lsp_fromJsonCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_Lsp_fromJsonCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_13 = l_Lean_Name_toString(x_12, x_8, x_6);
x_14 = lean_string_append(x_11, x_13);
lean_dec_ref(x_13);
x_15 = l_Lean_Lsp_fromJsonCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_alloc_closure((void*)(l_Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20____boxed), 1, 0);
x_20 = l_Lean_Lsp_fromJsonCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_21 = 1;
lean_inc_ref(x_19);
x_22 = l_Lean_Name_toString(x_20, x_21, x_19);
x_23 = l_Lean_Lsp_fromJsonCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lean_Lsp_fromJsonCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_26 = l_Lean_Name_toString(x_25, x_21, x_19);
x_27 = lean_string_append(x_24, x_26);
lean_dec_ref(x_26);
x_28 = l_Lean_Lsp_fromJsonCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_18);
lean_dec(x_18);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_ctor_set_tag(x_3, 0);
return x_3;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
lean_dec(x_3);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
return x_3;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_20__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_20__spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_fromJsonCompletionItemData___lam__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionItemData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_20_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionItemData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonCompletionItemData___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at___Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_87__spec__0(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Lsp_toJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_87_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_87_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Lean_Lsp_fromJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_;
x_3 = l_Lean_Lsp_toJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_3088_(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Lsp_toJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_87_;
x_10 = l_List_flatMapTR_go___at___Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_87__spec__0(x_8, x_9);
x_11 = l_Lean_Json_mkObj(x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonCompletionItemData___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_toJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_87_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonCompletionItemData() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonCompletionItemData___closed__0;
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.Completion.CompletionItemData", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Lsp.CompletionItem.getFileSource!", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no data param on completion item ", 33, 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_CompletionItem_getFileSource_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 6);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec_ref(x_11);
x_2 = x_13;
goto block_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec_ref(x_10);
x_15 = l_Lean_Lsp_fromJsonCompletionItemData____x40_Lean_Server_Completion_CompletionItemData___hyg_20_(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_2 = x_16;
goto block_9;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec(x_17);
return x_18;
}
}
block_9:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0;
x_4 = l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1;
x_5 = lean_unsigned_to_nat(38u);
x_6 = lean_unsigned_to_nat(22u);
x_7 = l_mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_2);
lean_dec_ref(x_2);
x_8 = l_panic___at___Lean_Lsp_CompletionItem_getFileSource_x21_spec__0(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCompletionItem___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Lsp_CompletionItem_getFileSource_x21), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFileSourceCompletionItem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFileSourceCompletionItem___closed__0;
return x_1;
}
}
lean_object* initialize_Lean_Server_FileSource(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionItemData(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_FileSource(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_fromJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_ = _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_20_);
l_Lean_Lsp_fromJsonCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionItemData___hyg_20_ = _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionItemData___hyg_20_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionItemData___closed__1____x40_Lean_Server_Completion_CompletionItemData___hyg_20_);
l_Lean_Lsp_fromJsonCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionItemData___hyg_20_ = _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionItemData___hyg_20_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionItemData___closed__2____x40_Lean_Server_Completion_CompletionItemData___hyg_20_);
l_Lean_Lsp_fromJsonCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionItemData___hyg_20_ = _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionItemData___hyg_20_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionItemData___closed__3____x40_Lean_Server_Completion_CompletionItemData___hyg_20_);
l_Lean_Lsp_fromJsonCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionItemData___hyg_20_ = _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionItemData___hyg_20_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionItemData___closed__4____x40_Lean_Server_Completion_CompletionItemData___hyg_20_);
l_Lean_Lsp_fromJsonCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionItemData___hyg_20_ = _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionItemData___hyg_20_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionItemData___closed__5____x40_Lean_Server_Completion_CompletionItemData___hyg_20_);
l_Lean_Lsp_fromJsonCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionItemData___hyg_20_ = _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionItemData___hyg_20_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionItemData___closed__6____x40_Lean_Server_Completion_CompletionItemData___hyg_20_);
l_Lean_Lsp_fromJsonCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionItemData___hyg_20_ = _init_l_Lean_Lsp_fromJsonCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionItemData___hyg_20_();
lean_mark_persistent(l_Lean_Lsp_fromJsonCompletionItemData___closed__7____x40_Lean_Server_Completion_CompletionItemData___hyg_20_);
l_Lean_Lsp_instFromJsonCompletionItemData___closed__0 = _init_l_Lean_Lsp_instFromJsonCompletionItemData___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFromJsonCompletionItemData___closed__0);
l_Lean_Lsp_instFromJsonCompletionItemData = _init_l_Lean_Lsp_instFromJsonCompletionItemData();
lean_mark_persistent(l_Lean_Lsp_instFromJsonCompletionItemData);
l_Lean_Lsp_toJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_87_ = _init_l_Lean_Lsp_toJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_87_();
lean_mark_persistent(l_Lean_Lsp_toJsonCompletionItemData___closed__0____x40_Lean_Server_Completion_CompletionItemData___hyg_87_);
l_Lean_Lsp_instToJsonCompletionItemData___closed__0 = _init_l_Lean_Lsp_instToJsonCompletionItemData___closed__0();
lean_mark_persistent(l_Lean_Lsp_instToJsonCompletionItemData___closed__0);
l_Lean_Lsp_instToJsonCompletionItemData = _init_l_Lean_Lsp_instToJsonCompletionItemData();
lean_mark_persistent(l_Lean_Lsp_instToJsonCompletionItemData);
l_panic___at___Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0 = _init_l_panic___at___Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Lsp_CompletionItem_getFileSource_x21_spec__0___closed__0);
l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0 = _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__0);
l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1 = _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__1);
l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2 = _init_l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2();
lean_mark_persistent(l_Lean_Lsp_CompletionItem_getFileSource_x21___closed__2);
l_Lean_Lsp_instFileSourceCompletionItem___closed__0 = _init_l_Lean_Lsp_instFileSourceCompletionItem___closed__0();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCompletionItem___closed__0);
l_Lean_Lsp_instFileSourceCompletionItem = _init_l_Lean_Lsp_instFileSourceCompletionItem();
lean_mark_persistent(l_Lean_Lsp_instFileSourceCompletionItem);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
