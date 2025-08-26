// Lean compiler output
// Module: Lake.Toml.Load
// Imports: Lean.Message Lean.Parser.Types Lake.Toml.Data.Value Lean.Parser Lake.Toml.Elab Lake.Util.Message
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
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__18;
static lean_object* l_Lake_Toml_loadToml___closed__29;
static lean_object* l_Lake_Toml_loadToml___closed__12;
static lean_object* l_Lake_Toml_loadToml___closed__17;
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__24;
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__16;
static lean_object* l_Lake_Toml_loadToml___closed__13;
static lean_object* l_Lake_Toml_loadToml___closed__20;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__3;
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lake_Toml_toml;
static lean_object* l_Lake_Toml_loadToml___closed__21;
static lean_object* l_Lake_Toml_loadToml___closed__14;
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__11;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__28;
static lean_object* l_Lake_Toml_loadToml___closed__1;
static lean_object* l_Lake_Toml_loadToml___closed__26;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__8;
static lean_object* l_Lake_Toml_loadToml___closed__27;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__22;
static lean_object* l_Lake_Toml_loadToml___closed__2;
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
static lean_object* l_Lake_Toml_loadToml___closed__15;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lake_Toml_loadToml___closed__23;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lake_Toml_loadToml___closed__6;
static lean_object* l_Lake_Toml_loadToml___closed__5;
static lean_object* l_Lake_Toml_loadToml___closed__4;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__9;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__10;
static lean_object* l_Lake_Toml_loadToml___closed__0;
static lean_object* l_Lake_Toml_loadToml___closed__7;
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__19;
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__25;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_toml;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Data_Trie_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("end of input", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_loadToml___closed__4;
x_2 = l_Lake_Toml_loadToml___closed__2;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageLog_empty;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_firstFrontendMacroScope;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lake_Toml_loadToml___closed__7;
x_3 = lean_nat_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lake_Toml_loadToml___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__15() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Toml_loadToml___closed__13;
x_4 = l_Lake_Toml_loadToml___closed__14;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__16() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___closed__15;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__18;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___closed__20;
x_2 = l_Lake_Toml_loadToml___closed__15;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to initialize TOML environment: ", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__27;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_mk_empty_environment(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lake_Toml_loadToml___closed__0;
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_box(0);
x_14 = lean_box(0);
lean_inc(x_6);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_13);
x_16 = l_Lake_Toml_loadToml___closed__1;
x_17 = l_Lean_Parser_mkParserState(x_10);
lean_inc_ref(x_1);
x_18 = l_Lean_Parser_ParserFn_run(x_9, x_1, x_15, x_16, x_17);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = l_Lean_Parser_InputContext_atEnd(x_1, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_20);
lean_dec(x_6);
x_23 = l_Lake_Toml_loadToml___closed__5;
x_24 = l_Lake_mkParserErrorMessage(x_1, x_18, x_23);
lean_dec_ref(x_18);
x_25 = l_Lake_Toml_loadToml___closed__6;
x_26 = l_Lean_MessageLog_add(x_24, x_25);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_26);
return x_4;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_89; uint8_t x_112; 
lean_dec_ref(x_18);
lean_free_object(x_4);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lake_Toml_loadToml___closed__7;
x_29 = l_Lake_Toml_loadToml___closed__8;
x_30 = l_Lake_Toml_loadToml___closed__11;
x_31 = l_Lake_Toml_loadToml___closed__12;
x_32 = l_Lake_Toml_loadToml___closed__15;
x_33 = l_Lake_Toml_loadToml___closed__16;
x_34 = l_Lake_Toml_loadToml___closed__18;
x_35 = l_Lake_Toml_loadToml___closed__19;
x_36 = l_Lake_Toml_loadToml___closed__21;
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_22);
x_38 = l_Lake_Toml_loadToml___closed__22;
x_39 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_39, 0, x_6);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_30);
lean_ctor_set(x_39, 3, x_31);
lean_ctor_set(x_39, 4, x_33);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_36);
lean_ctor_set(x_39, 7, x_37);
lean_ctor_set(x_39, 8, x_38);
x_40 = lean_st_mk_ref(x_39, x_7);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l_Lake_Toml_loadToml___closed__23;
x_44 = lean_st_ref_get(x_43, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_st_ref_get(x_41, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_50);
lean_dec(x_48);
x_51 = l_Lean_Parser_SyntaxStack_back(x_20);
lean_dec_ref(x_20);
x_52 = lean_box(0);
x_53 = l_Lake_Toml_loadToml___closed__24;
x_54 = 0;
x_55 = lean_box(0);
x_56 = l_Lake_Toml_loadToml___closed__25;
x_57 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0(x_13, x_56);
x_112 = l_Lean_Kernel_isDiagnosticsEnabled(x_50);
lean_dec_ref(x_50);
if (x_112 == 0)
{
if (x_57 == 0)
{
x_89 = x_22;
goto block_111;
}
else
{
x_89 = x_112;
goto block_111;
}
}
else
{
x_89 = x_57;
goto block_111;
}
block_88:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l_Lake_Toml_loadToml___closed__26;
x_61 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1(x_13, x_60);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_62 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_62, 0, x_11);
lean_ctor_set(x_62, 1, x_12);
lean_ctor_set(x_62, 2, x_13);
lean_ctor_set(x_62, 3, x_27);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_52);
lean_ctor_set(x_62, 6, x_14);
lean_ctor_set(x_62, 7, x_13);
lean_ctor_set(x_62, 8, x_27);
lean_ctor_set(x_62, 9, x_53);
lean_ctor_set(x_62, 10, x_14);
lean_ctor_set(x_62, 11, x_28);
lean_ctor_set(x_62, 12, x_55);
lean_ctor_set(x_62, 13, x_45);
lean_ctor_set_uint8(x_62, sizeof(void*)*14, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*14 + 1, x_54);
x_63 = l_Lake_Toml_elabToml(x_51, x_62, x_58, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec_ref(x_1);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = lean_st_ref_get(x_41, x_65);
lean_dec(x_41);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_68, 6);
lean_inc_ref(x_69);
lean_dec(x_68);
x_70 = l_Lean_MessageLog_hasErrors(x_69);
if (x_70 == 0)
{
lean_dec_ref(x_69);
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
else
{
lean_dec(x_64);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_66);
x_73 = lean_ctor_get(x_71, 6);
lean_inc_ref(x_73);
lean_dec(x_71);
x_74 = l_Lean_MessageLog_hasErrors(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec_ref(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_64);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_41);
x_77 = !lean_is_exclusive(x_63);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_63, 0);
x_79 = l_Lake_mkExceptionMessage(x_1, x_78);
x_80 = l_Lake_Toml_loadToml___closed__6;
x_81 = l_Lean_MessageLog_add(x_79, x_80);
lean_ctor_set(x_63, 0, x_81);
return x_63;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_63, 0);
x_83 = lean_ctor_get(x_63, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_63);
x_84 = l_Lake_mkExceptionMessage(x_1, x_82);
x_85 = l_Lake_Toml_loadToml___closed__6;
x_86 = l_Lean_MessageLog_add(x_84, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
}
block_111:
{
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_st_ref_take(x_41, x_49);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = !lean_is_exclusive(x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_91, 0);
x_95 = lean_ctor_get(x_91, 5);
lean_dec(x_95);
x_96 = l_Lean_Kernel_enableDiag(x_94, x_57);
lean_ctor_set(x_91, 5, x_35);
lean_ctor_set(x_91, 0, x_96);
x_97 = lean_st_ref_set(x_41, x_91, x_92);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
lean_inc(x_41);
x_58 = x_41;
x_59 = x_98;
goto block_88;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_99 = lean_ctor_get(x_91, 0);
x_100 = lean_ctor_get(x_91, 1);
x_101 = lean_ctor_get(x_91, 2);
x_102 = lean_ctor_get(x_91, 3);
x_103 = lean_ctor_get(x_91, 4);
x_104 = lean_ctor_get(x_91, 6);
x_105 = lean_ctor_get(x_91, 7);
x_106 = lean_ctor_get(x_91, 8);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_91);
x_107 = l_Lean_Kernel_enableDiag(x_99, x_57);
x_108 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_100);
lean_ctor_set(x_108, 2, x_101);
lean_ctor_set(x_108, 3, x_102);
lean_ctor_set(x_108, 4, x_103);
lean_ctor_set(x_108, 5, x_35);
lean_ctor_set(x_108, 6, x_104);
lean_ctor_set(x_108, 7, x_105);
lean_ctor_set(x_108, 8, x_106);
x_109 = lean_st_ref_set(x_41, x_108, x_92);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec_ref(x_109);
lean_inc(x_41);
x_58 = x_41;
x_59 = x_110;
goto block_88;
}
}
else
{
lean_inc(x_41);
x_58 = x_41;
x_59 = x_49;
goto block_88;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_6);
x_113 = lean_ctor_get(x_19, 0);
lean_inc(x_113);
lean_dec_ref(x_19);
x_114 = l_Lake_mkParserErrorMessage(x_1, x_18, x_113);
lean_dec_ref(x_18);
x_115 = l_Lake_Toml_loadToml___closed__6;
x_116 = l_Lean_MessageLog_add(x_114, x_115);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_116);
return x_4;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_119 = l_Lake_Toml_loadToml___closed__0;
x_120 = lean_ctor_get(x_119, 1);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_1, 0);
x_122 = lean_ctor_get(x_1, 1);
x_123 = lean_ctor_get(x_1, 2);
x_124 = lean_box(0);
x_125 = lean_box(0);
lean_inc(x_117);
x_126 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_126, 0, x_117);
lean_ctor_set(x_126, 1, x_124);
lean_ctor_set(x_126, 2, x_125);
lean_ctor_set(x_126, 3, x_124);
x_127 = l_Lake_Toml_loadToml___closed__1;
x_128 = l_Lean_Parser_mkParserState(x_121);
lean_inc_ref(x_1);
x_129 = l_Lean_Parser_ParserFn_run(x_120, x_1, x_126, x_127, x_128);
x_130 = lean_ctor_get(x_129, 4);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_129, 0);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_129, 2);
lean_inc(x_132);
x_133 = l_Lean_Parser_InputContext_atEnd(x_1, x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_131);
lean_dec(x_117);
x_134 = l_Lake_Toml_loadToml___closed__5;
x_135 = l_Lake_mkParserErrorMessage(x_1, x_129, x_134);
lean_dec_ref(x_129);
x_136 = l_Lake_Toml_loadToml___closed__6;
x_137 = l_Lean_MessageLog_add(x_135, x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_118);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; uint8_t x_194; uint8_t x_212; 
lean_dec_ref(x_129);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l_Lake_Toml_loadToml___closed__7;
x_141 = l_Lake_Toml_loadToml___closed__8;
x_142 = l_Lake_Toml_loadToml___closed__11;
x_143 = l_Lake_Toml_loadToml___closed__12;
x_144 = l_Lake_Toml_loadToml___closed__15;
x_145 = l_Lake_Toml_loadToml___closed__16;
x_146 = l_Lake_Toml_loadToml___closed__18;
x_147 = l_Lake_Toml_loadToml___closed__19;
x_148 = l_Lake_Toml_loadToml___closed__21;
x_149 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_146);
lean_ctor_set(x_149, 2, x_144);
lean_ctor_set_uint8(x_149, sizeof(void*)*3, x_133);
x_150 = l_Lake_Toml_loadToml___closed__22;
x_151 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_151, 0, x_117);
lean_ctor_set(x_151, 1, x_141);
lean_ctor_set(x_151, 2, x_142);
lean_ctor_set(x_151, 3, x_143);
lean_ctor_set(x_151, 4, x_145);
lean_ctor_set(x_151, 5, x_147);
lean_ctor_set(x_151, 6, x_148);
lean_ctor_set(x_151, 7, x_149);
lean_ctor_set(x_151, 8, x_150);
x_152 = lean_st_mk_ref(x_151, x_118);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec_ref(x_152);
x_155 = l_Lake_Toml_loadToml___closed__23;
x_156 = lean_st_ref_get(x_155, x_154);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec_ref(x_156);
x_159 = lean_st_ref_get(x_153, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_162);
lean_dec(x_160);
x_163 = l_Lean_Parser_SyntaxStack_back(x_131);
lean_dec_ref(x_131);
x_164 = lean_box(0);
x_165 = l_Lake_Toml_loadToml___closed__24;
x_166 = 0;
x_167 = lean_box(0);
x_168 = l_Lake_Toml_loadToml___closed__25;
x_169 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0(x_124, x_168);
x_212 = l_Lean_Kernel_isDiagnosticsEnabled(x_162);
lean_dec_ref(x_162);
if (x_212 == 0)
{
if (x_169 == 0)
{
x_194 = x_133;
goto block_211;
}
else
{
x_194 = x_212;
goto block_211;
}
}
else
{
x_194 = x_169;
goto block_211;
}
block_193:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = l_Lake_Toml_loadToml___closed__26;
x_173 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1(x_124, x_172);
lean_inc_ref(x_123);
lean_inc_ref(x_122);
x_174 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_174, 0, x_122);
lean_ctor_set(x_174, 1, x_123);
lean_ctor_set(x_174, 2, x_124);
lean_ctor_set(x_174, 3, x_139);
lean_ctor_set(x_174, 4, x_173);
lean_ctor_set(x_174, 5, x_164);
lean_ctor_set(x_174, 6, x_125);
lean_ctor_set(x_174, 7, x_124);
lean_ctor_set(x_174, 8, x_139);
lean_ctor_set(x_174, 9, x_165);
lean_ctor_set(x_174, 10, x_125);
lean_ctor_set(x_174, 11, x_140);
lean_ctor_set(x_174, 12, x_167);
lean_ctor_set(x_174, 13, x_157);
lean_ctor_set_uint8(x_174, sizeof(void*)*14, x_169);
lean_ctor_set_uint8(x_174, sizeof(void*)*14 + 1, x_166);
x_175 = l_Lake_Toml_elabToml(x_163, x_174, x_170, x_171);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_dec_ref(x_1);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec_ref(x_175);
x_178 = lean_st_ref_get(x_153, x_177);
lean_dec(x_153);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_179, 6);
lean_inc_ref(x_182);
lean_dec(x_179);
x_183 = l_Lean_MessageLog_hasErrors(x_182);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec_ref(x_182);
if (lean_is_scalar(x_181)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_181;
}
lean_ctor_set(x_184, 0, x_176);
lean_ctor_set(x_184, 1, x_180);
return x_184;
}
else
{
lean_object* x_185; 
lean_dec(x_176);
if (lean_is_scalar(x_181)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_181;
 lean_ctor_set_tag(x_185, 1);
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_180);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_153);
x_186 = lean_ctor_get(x_175, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_175, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_188 = x_175;
} else {
 lean_dec_ref(x_175);
 x_188 = lean_box(0);
}
x_189 = l_Lake_mkExceptionMessage(x_1, x_186);
x_190 = l_Lake_Toml_loadToml___closed__6;
x_191 = l_Lean_MessageLog_add(x_189, x_190);
if (lean_is_scalar(x_188)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_188;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_187);
return x_192;
}
}
block_211:
{
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_195 = lean_st_ref_take(x_153, x_161);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec_ref(x_195);
x_198 = lean_ctor_get(x_196, 0);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 2);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_196, 3);
lean_inc_ref(x_201);
x_202 = lean_ctor_get(x_196, 4);
lean_inc_ref(x_202);
x_203 = lean_ctor_get(x_196, 6);
lean_inc_ref(x_203);
x_204 = lean_ctor_get(x_196, 7);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_196, 8);
lean_inc_ref(x_205);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 lean_ctor_release(x_196, 5);
 lean_ctor_release(x_196, 6);
 lean_ctor_release(x_196, 7);
 lean_ctor_release(x_196, 8);
 x_206 = x_196;
} else {
 lean_dec_ref(x_196);
 x_206 = lean_box(0);
}
x_207 = l_Lean_Kernel_enableDiag(x_198, x_169);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 9, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_199);
lean_ctor_set(x_208, 2, x_200);
lean_ctor_set(x_208, 3, x_201);
lean_ctor_set(x_208, 4, x_202);
lean_ctor_set(x_208, 5, x_147);
lean_ctor_set(x_208, 6, x_203);
lean_ctor_set(x_208, 7, x_204);
lean_ctor_set(x_208, 8, x_205);
x_209 = lean_st_ref_set(x_153, x_208, x_197);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec_ref(x_209);
lean_inc(x_153);
x_170 = x_153;
x_171 = x_210;
goto block_193;
}
else
{
lean_inc(x_153);
x_170 = x_153;
x_171 = x_161;
goto block_193;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_117);
x_213 = lean_ctor_get(x_130, 0);
lean_inc(x_213);
lean_dec_ref(x_130);
x_214 = l_Lake_mkParserErrorMessage(x_1, x_129, x_213);
lean_dec_ref(x_129);
x_215 = l_Lake_Toml_loadToml___closed__6;
x_216 = l_Lean_MessageLog_add(x_214, x_215);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_118);
return x_217;
}
}
}
else
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_4);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_219 = lean_ctor_get(x_4, 0);
x_220 = l_Lake_Toml_loadToml___closed__28;
x_221 = lean_io_error_to_string(x_219);
x_222 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = l_Lean_MessageData_ofFormat(x_222);
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_220);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lake_Toml_loadToml___closed__29;
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = 2;
x_228 = l_Lake_mkMessageNoPos(x_1, x_226, x_227);
x_229 = l_Lake_Toml_loadToml___closed__6;
x_230 = l_Lean_MessageLog_add(x_228, x_229);
lean_ctor_set(x_4, 0, x_230);
return x_4;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_231 = lean_ctor_get(x_4, 0);
x_232 = lean_ctor_get(x_4, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_4);
x_233 = l_Lake_Toml_loadToml___closed__28;
x_234 = lean_io_error_to_string(x_231);
x_235 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_236 = l_Lean_MessageData_ofFormat(x_235);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_233);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Lake_Toml_loadToml___closed__29;
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = 2;
x_241 = l_Lake_mkMessageNoPos(x_1, x_239, x_240);
x_242 = l_Lake_Toml_loadToml___closed__6;
x_243 = l_Lean_MessageLog_add(x_241, x_242);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_232);
return x_244;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___Lake_Toml_loadToml_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Load(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_Value(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Toml_loadToml___closed__0 = _init_l_Lake_Toml_loadToml___closed__0();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__0);
l_Lake_Toml_loadToml___closed__1 = _init_l_Lake_Toml_loadToml___closed__1();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__1);
l_Lake_Toml_loadToml___closed__2 = _init_l_Lake_Toml_loadToml___closed__2();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__2);
l_Lake_Toml_loadToml___closed__3 = _init_l_Lake_Toml_loadToml___closed__3();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__3);
l_Lake_Toml_loadToml___closed__4 = _init_l_Lake_Toml_loadToml___closed__4();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__4);
l_Lake_Toml_loadToml___closed__5 = _init_l_Lake_Toml_loadToml___closed__5();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__5);
l_Lake_Toml_loadToml___closed__6 = _init_l_Lake_Toml_loadToml___closed__6();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__6);
l_Lake_Toml_loadToml___closed__7 = _init_l_Lake_Toml_loadToml___closed__7();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__7);
l_Lake_Toml_loadToml___closed__8 = _init_l_Lake_Toml_loadToml___closed__8();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__8);
l_Lake_Toml_loadToml___closed__9 = _init_l_Lake_Toml_loadToml___closed__9();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__9);
l_Lake_Toml_loadToml___closed__10 = _init_l_Lake_Toml_loadToml___closed__10();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__10);
l_Lake_Toml_loadToml___closed__11 = _init_l_Lake_Toml_loadToml___closed__11();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__11);
l_Lake_Toml_loadToml___closed__12 = _init_l_Lake_Toml_loadToml___closed__12();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__12);
l_Lake_Toml_loadToml___closed__13 = _init_l_Lake_Toml_loadToml___closed__13();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__13);
l_Lake_Toml_loadToml___closed__14 = _init_l_Lake_Toml_loadToml___closed__14();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__14);
l_Lake_Toml_loadToml___closed__15 = _init_l_Lake_Toml_loadToml___closed__15();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__15);
l_Lake_Toml_loadToml___closed__16 = _init_l_Lake_Toml_loadToml___closed__16();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__16);
l_Lake_Toml_loadToml___closed__17 = _init_l_Lake_Toml_loadToml___closed__17();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__17);
l_Lake_Toml_loadToml___closed__18 = _init_l_Lake_Toml_loadToml___closed__18();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__18);
l_Lake_Toml_loadToml___closed__19 = _init_l_Lake_Toml_loadToml___closed__19();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__19);
l_Lake_Toml_loadToml___closed__20 = _init_l_Lake_Toml_loadToml___closed__20();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__20);
l_Lake_Toml_loadToml___closed__21 = _init_l_Lake_Toml_loadToml___closed__21();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__21);
l_Lake_Toml_loadToml___closed__22 = _init_l_Lake_Toml_loadToml___closed__22();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__22);
l_Lake_Toml_loadToml___closed__23 = _init_l_Lake_Toml_loadToml___closed__23();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__23);
l_Lake_Toml_loadToml___closed__24 = _init_l_Lake_Toml_loadToml___closed__24();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__24);
l_Lake_Toml_loadToml___closed__25 = _init_l_Lake_Toml_loadToml___closed__25();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__25);
l_Lake_Toml_loadToml___closed__26 = _init_l_Lake_Toml_loadToml___closed__26();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__26);
l_Lake_Toml_loadToml___closed__27 = _init_l_Lake_Toml_loadToml___closed__27();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__27);
l_Lake_Toml_loadToml___closed__28 = _init_l_Lake_Toml_loadToml___closed__28();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__28);
l_Lake_Toml_loadToml___closed__29 = _init_l_Lake_Toml_loadToml___closed__29();
lean_mark_persistent(l_Lake_Toml_loadToml___closed__29);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
