// Lean compiler output
// Module: Lake.Util.Name
// Imports: public import Lean.Data.Json public import Lake.Util.RBArray import Init.Data.Ord.String import Init.Data.Ord.UInt import all Init.Prelude import all Lean.Data.Name
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NameMap_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_OrdNameMap_empty___closed__1;
LEAN_EXPORT lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Name_eraseHead(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0;
static lean_object* l_Lake_OrdNameMap_empty___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBArray_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap(lean_object*);
lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_stringToLegalOrSimpleName(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
lean_inc_ref(x_1);
x_2 = l_String_toName(x_1);
x_3 = l_Lean_Name_isAnonymous(x_2);
if (x_3 == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Name_str___override(x_4, x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NameMap_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0;
return x_2;
}
}
static lean_object* _init_l_Lake_OrdNameMap_empty___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_OrdNameMap_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_OrdNameMap_empty___closed__0;
x_2 = l_Lake_RBArray_empty(lean_box(0), lean_box(0), x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdNameMap_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OrdNameMap_empty___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkOrdNameMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_OrdNameMap_empty___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_DNameMap_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_eraseHead(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_1;
}
case 1:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lake_Name_eraseHead(x_2);
x_5 = l_Lean_Name_str___override(x_4, x_3);
return x_5;
}
}
default: 
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec_ref(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lake_Name_eraseHead(x_6);
x_9 = l_Lean_Name_num___override(x_8, x_7);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = lean_apply_3(x_5, x_1, x_7, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_apply_3(x_4, x_1, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_4, x_2);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_3);
x_10 = lean_apply_3(x_6, x_2, x_8, x_9);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = lean_apply_3(x_5, x_2, x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = lean_apply_3(x_4, x_1, x_7, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_apply_3(x_5, x_1, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_apply_2(x_4, x_2, lean_box(0));
return x_12;
}
}
case 1:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_apply_2(x_5, x_1, lean_box(0));
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_5);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_2);
x_18 = lean_apply_4(x_9, x_14, x_15, x_16, x_17);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_5);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec_ref(x_2);
x_23 = lean_apply_4(x_8, x_19, x_20, x_21, x_22);
return x_23;
}
}
}
default: 
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
x_24 = lean_apply_2(x_5, x_1, lean_box(0));
return x_24;
}
case 1:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_2);
x_29 = lean_apply_4(x_7, x_25, x_26, x_27, x_28);
return x_29;
}
default: 
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_5);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_dec_ref(x_2);
x_34 = lean_apply_4(x_6, x_30, x_31, x_32, x_33);
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_apply_2(x_5, x_3, lean_box(0));
return x_13;
}
}
case 1:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
x_14 = lean_apply_2(x_6, x_2, lean_box(0));
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_6);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_3);
x_19 = lean_apply_4(x_10, x_15, x_16, x_17, x_18);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_6);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_21);
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec_ref(x_3);
x_24 = lean_apply_4(x_9, x_20, x_21, x_22, x_23);
return x_24;
}
}
}
default: 
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
x_25 = lean_apply_2(x_6, x_2, lean_box(0));
return x_25;
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
lean_dec(x_6);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec_ref(x_2);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_29);
lean_dec_ref(x_3);
x_30 = lean_apply_4(x_8, x_26, x_27, x_28, x_29);
return x_30;
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_6);
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_dec_ref(x_2);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_dec_ref(x_3);
x_35 = lean_apply_4(x_7, x_31, x_32, x_33, x_34);
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(x_1);
x_7 = lean_apply_2(x_3, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(x_2);
x_8 = lean_apply_2(x_4, x_7, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_SourceInfo_fromRef(x_1, x_3);
x_5 = l_Lean_Syntax_setHeadInfo(x_1, x_4);
x_6 = l_Lean_instQuoteNameMkStr1___private__1(x_2);
x_7 = l_Lean_Syntax_copyHeadTailInfoFrom(x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Name_quoteFrom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lake_Name_quoteFrom(x_1, x_2, x_4);
return x_5;
}
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Lake_Util_RBArray(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_String(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Lean_Data_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Name(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_RBArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0 = _init_l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0();
lean_mark_persistent(l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0);
l_Lake_OrdNameMap_empty___closed__0 = _init_l_Lake_OrdNameMap_empty___closed__0();
lean_mark_persistent(l_Lake_OrdNameMap_empty___closed__0);
l_Lake_OrdNameMap_empty___closed__1 = _init_l_Lake_OrdNameMap_empty___closed__1();
lean_mark_persistent(l_Lake_OrdNameMap_empty___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
