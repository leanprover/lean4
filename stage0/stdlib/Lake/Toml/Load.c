// Lean compiler output
// Module: Lake.Toml.Load
// Imports: public import Lean.Parser.Types public import Lake.Toml.Data.Value import Lean.Parser import Lake.Toml.Elab import Lake.Util.Message
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
static lean_object* l_Lake_Toml_loadToml___closed__12;
static lean_object* l_Lake_Toml_loadToml___closed__17;
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__28;
static lean_object* l_Lake_Toml_loadToml___closed__1;
static lean_object* l_Lake_Toml_loadToml___closed__26;
lean_object* lean_st_ref_take(lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__8;
static lean_object* l_Lake_Toml_loadToml___closed__27;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__22;
static lean_object* l_Lake_Toml_loadToml___closed__2;
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
static lean_object* l_Lake_Toml_loadToml___closed__15;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lake_Toml_loadToml___closed__23;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lake_Toml_loadToml___closed__6;
static lean_object* l_Lake_Toml_loadToml___closed__5;
static lean_object* l_Lake_Toml_loadToml___closed__4;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__9;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__10;
static lean_object* l_Lake_Toml_loadToml___closed__0;
static lean_object* l_Lake_Toml_loadToml___closed__7;
lean_object* lean_mk_empty_environment(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__19;
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__25;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = lean_mk_empty_environment(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lake_Toml_loadToml___closed__0;
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_box(0);
x_13 = lean_box(0);
lean_inc(x_6);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
x_15 = l_Lake_Toml_loadToml___closed__1;
x_16 = l_Lean_Parser_mkParserState(x_9);
lean_inc_ref(x_1);
x_17 = l_Lean_Parser_ParserFn_run(x_8, x_1, x_14, x_15, x_16);
x_18 = lean_ctor_get(x_17, 4);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
x_21 = l_Lean_Parser_InputContext_atEnd(x_1, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_19);
lean_dec(x_6);
x_22 = l_Lake_Toml_loadToml___closed__5;
x_23 = l_Lake_mkParserErrorMessage(x_1, x_17, x_22);
lean_dec_ref(x_17);
x_24 = l_Lake_Toml_loadToml___closed__6;
x_25 = l_Lean_MessageLog_add(x_23, x_24);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_79; uint8_t x_98; 
lean_dec_ref(x_17);
lean_free_object(x_4);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lake_Toml_loadToml___closed__7;
x_28 = l_Lake_Toml_loadToml___closed__8;
x_29 = l_Lake_Toml_loadToml___closed__11;
x_30 = l_Lake_Toml_loadToml___closed__12;
x_31 = l_Lake_Toml_loadToml___closed__15;
x_32 = l_Lake_Toml_loadToml___closed__16;
x_33 = l_Lake_Toml_loadToml___closed__18;
x_34 = l_Lake_Toml_loadToml___closed__19;
x_35 = l_Lake_Toml_loadToml___closed__21;
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_21);
x_37 = l_Lake_Toml_loadToml___closed__22;
x_38 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_29);
lean_ctor_set(x_38, 3, x_30);
lean_ctor_set(x_38, 4, x_32);
lean_ctor_set(x_38, 5, x_34);
lean_ctor_set(x_38, 6, x_35);
lean_ctor_set(x_38, 7, x_36);
lean_ctor_set(x_38, 8, x_37);
x_39 = lean_st_mk_ref(x_38);
x_40 = l_Lake_Toml_loadToml___closed__23;
x_41 = lean_st_ref_get(x_40);
x_42 = lean_st_ref_get(x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_Parser_SyntaxStack_back(x_19);
lean_dec_ref(x_19);
x_45 = lean_box(0);
x_46 = l_Lake_Toml_loadToml___closed__24;
x_47 = 0;
x_48 = lean_box(0);
x_49 = l_Lake_Toml_loadToml___closed__25;
x_50 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(x_12, x_49);
x_98 = l_Lean_Kernel_isDiagnosticsEnabled(x_43);
lean_dec_ref(x_43);
if (x_98 == 0)
{
if (x_50 == 0)
{
x_79 = x_21;
goto block_97;
}
else
{
x_79 = x_98;
goto block_97;
}
}
else
{
x_79 = x_50;
goto block_97;
}
block_78:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = l_Lake_Toml_loadToml___closed__26;
x_54 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(x_12, x_53);
lean_inc_ref(x_11);
lean_inc_ref(x_10);
x_55 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_11);
lean_ctor_set(x_55, 2, x_12);
lean_ctor_set(x_55, 3, x_26);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_45);
lean_ctor_set(x_55, 6, x_13);
lean_ctor_set(x_55, 7, x_12);
lean_ctor_set(x_55, 8, x_26);
lean_ctor_set(x_55, 9, x_46);
lean_ctor_set(x_55, 10, x_13);
lean_ctor_set(x_55, 11, x_27);
lean_ctor_set(x_55, 12, x_48);
lean_ctor_set(x_55, 13, x_41);
lean_ctor_set_uint8(x_55, sizeof(void*)*14, x_50);
lean_ctor_set_uint8(x_55, sizeof(void*)*14 + 1, x_47);
x_56 = l_Lake_Toml_elabToml(x_44, x_55, x_51);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_st_ref_get(x_39);
lean_dec(x_39);
x_60 = lean_ctor_get(x_59, 6);
lean_inc_ref(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_MessageLog_hasErrors(x_60);
if (x_61 == 0)
{
lean_dec_ref(x_60);
return x_56;
}
else
{
lean_dec(x_58);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_st_ref_get(x_39);
lean_dec(x_39);
x_64 = lean_ctor_get(x_63, 6);
lean_inc_ref(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_MessageLog_hasErrors(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec_ref(x_64);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_62);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_62);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_64);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_39);
x_68 = !lean_is_exclusive(x_56);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_56, 0);
x_70 = l_Lake_mkExceptionMessage(x_1, x_69);
x_71 = l_Lake_Toml_loadToml___closed__6;
x_72 = l_Lean_MessageLog_add(x_70, x_71);
lean_ctor_set(x_56, 0, x_72);
return x_56;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_56, 0);
lean_inc(x_73);
lean_dec(x_56);
x_74 = l_Lake_mkExceptionMessage(x_1, x_73);
x_75 = l_Lake_Toml_loadToml___closed__6;
x_76 = l_Lean_MessageLog_add(x_74, x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
block_97:
{
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_st_ref_take(x_39);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 5);
lean_dec(x_83);
x_84 = l_Lean_Kernel_enableDiag(x_82, x_50);
lean_ctor_set(x_80, 5, x_34);
lean_ctor_set(x_80, 0, x_84);
x_85 = lean_st_ref_set(x_39, x_80);
lean_inc(x_39);
x_51 = x_39;
x_52 = lean_box(0);
goto block_78;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_86 = lean_ctor_get(x_80, 0);
x_87 = lean_ctor_get(x_80, 1);
x_88 = lean_ctor_get(x_80, 2);
x_89 = lean_ctor_get(x_80, 3);
x_90 = lean_ctor_get(x_80, 4);
x_91 = lean_ctor_get(x_80, 6);
x_92 = lean_ctor_get(x_80, 7);
x_93 = lean_ctor_get(x_80, 8);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_80);
x_94 = l_Lean_Kernel_enableDiag(x_86, x_50);
x_95 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_87);
lean_ctor_set(x_95, 2, x_88);
lean_ctor_set(x_95, 3, x_89);
lean_ctor_set(x_95, 4, x_90);
lean_ctor_set(x_95, 5, x_34);
lean_ctor_set(x_95, 6, x_91);
lean_ctor_set(x_95, 7, x_92);
lean_ctor_set(x_95, 8, x_93);
x_96 = lean_st_ref_set(x_39, x_95);
lean_inc(x_39);
x_51 = x_39;
x_52 = lean_box(0);
goto block_78;
}
}
else
{
lean_inc(x_39);
x_51 = x_39;
x_52 = lean_box(0);
goto block_78;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_6);
x_99 = lean_ctor_get(x_18, 0);
lean_inc(x_99);
lean_dec_ref(x_18);
x_100 = l_Lake_mkParserErrorMessage(x_1, x_17, x_99);
lean_dec_ref(x_17);
x_101 = l_Lake_Toml_loadToml___closed__6;
x_102 = l_Lean_MessageLog_add(x_100, x_101);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_102);
return x_4;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_103 = lean_ctor_get(x_4, 0);
lean_inc(x_103);
lean_dec(x_4);
x_104 = l_Lake_Toml_loadToml___closed__0;
x_105 = lean_ctor_get(x_104, 1);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_1, 0);
x_107 = lean_ctor_get(x_1, 1);
x_108 = lean_ctor_get(x_1, 2);
x_109 = lean_box(0);
x_110 = lean_box(0);
lean_inc(x_103);
x_111 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_109);
lean_ctor_set(x_111, 2, x_110);
lean_ctor_set(x_111, 3, x_109);
x_112 = l_Lake_Toml_loadToml___closed__1;
x_113 = l_Lean_Parser_mkParserState(x_106);
lean_inc_ref(x_1);
x_114 = l_Lean_Parser_ParserFn_run(x_105, x_1, x_111, x_112, x_113);
x_115 = lean_ctor_get(x_114, 4);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_114, 2);
lean_inc(x_117);
x_118 = l_Lean_Parser_InputContext_atEnd(x_1, x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_116);
lean_dec(x_103);
x_119 = l_Lake_Toml_loadToml___closed__5;
x_120 = l_Lake_mkParserErrorMessage(x_1, x_114, x_119);
lean_dec_ref(x_114);
x_121 = l_Lake_Toml_loadToml___closed__6;
x_122 = l_Lean_MessageLog_add(x_120, x_121);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; uint8_t x_169; uint8_t x_184; 
lean_dec_ref(x_114);
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Lake_Toml_loadToml___closed__7;
x_126 = l_Lake_Toml_loadToml___closed__8;
x_127 = l_Lake_Toml_loadToml___closed__11;
x_128 = l_Lake_Toml_loadToml___closed__12;
x_129 = l_Lake_Toml_loadToml___closed__15;
x_130 = l_Lake_Toml_loadToml___closed__16;
x_131 = l_Lake_Toml_loadToml___closed__18;
x_132 = l_Lake_Toml_loadToml___closed__19;
x_133 = l_Lake_Toml_loadToml___closed__21;
x_134 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_131);
lean_ctor_set(x_134, 2, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*3, x_118);
x_135 = l_Lake_Toml_loadToml___closed__22;
x_136 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_136, 0, x_103);
lean_ctor_set(x_136, 1, x_126);
lean_ctor_set(x_136, 2, x_127);
lean_ctor_set(x_136, 3, x_128);
lean_ctor_set(x_136, 4, x_130);
lean_ctor_set(x_136, 5, x_132);
lean_ctor_set(x_136, 6, x_133);
lean_ctor_set(x_136, 7, x_134);
lean_ctor_set(x_136, 8, x_135);
x_137 = lean_st_mk_ref(x_136);
x_138 = l_Lake_Toml_loadToml___closed__23;
x_139 = lean_st_ref_get(x_138);
x_140 = lean_st_ref_get(x_137);
x_141 = lean_ctor_get(x_140, 0);
lean_inc_ref(x_141);
lean_dec_ref(x_140);
x_142 = l_Lean_Parser_SyntaxStack_back(x_116);
lean_dec_ref(x_116);
x_143 = lean_box(0);
x_144 = l_Lake_Toml_loadToml___closed__24;
x_145 = 0;
x_146 = lean_box(0);
x_147 = l_Lake_Toml_loadToml___closed__25;
x_148 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(x_109, x_147);
x_184 = l_Lean_Kernel_isDiagnosticsEnabled(x_141);
lean_dec_ref(x_141);
if (x_184 == 0)
{
if (x_148 == 0)
{
x_169 = x_118;
goto block_183;
}
else
{
x_169 = x_184;
goto block_183;
}
}
else
{
x_169 = x_148;
goto block_183;
}
block_168:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = l_Lake_Toml_loadToml___closed__26;
x_152 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(x_109, x_151);
lean_inc_ref(x_108);
lean_inc_ref(x_107);
x_153 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_153, 0, x_107);
lean_ctor_set(x_153, 1, x_108);
lean_ctor_set(x_153, 2, x_109);
lean_ctor_set(x_153, 3, x_124);
lean_ctor_set(x_153, 4, x_152);
lean_ctor_set(x_153, 5, x_143);
lean_ctor_set(x_153, 6, x_110);
lean_ctor_set(x_153, 7, x_109);
lean_ctor_set(x_153, 8, x_124);
lean_ctor_set(x_153, 9, x_144);
lean_ctor_set(x_153, 10, x_110);
lean_ctor_set(x_153, 11, x_125);
lean_ctor_set(x_153, 12, x_146);
lean_ctor_set(x_153, 13, x_139);
lean_ctor_set_uint8(x_153, sizeof(void*)*14, x_148);
lean_ctor_set_uint8(x_153, sizeof(void*)*14 + 1, x_145);
x_154 = l_Lake_Toml_elabToml(x_142, x_153, x_149);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
x_157 = lean_st_ref_get(x_137);
lean_dec(x_137);
x_158 = lean_ctor_get(x_157, 6);
lean_inc_ref(x_158);
lean_dec_ref(x_157);
x_159 = l_Lean_MessageLog_hasErrors(x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec_ref(x_158);
if (lean_is_scalar(x_156)) {
 x_160 = lean_alloc_ctor(0, 1, 0);
} else {
 x_160 = x_156;
}
lean_ctor_set(x_160, 0, x_155);
return x_160;
}
else
{
lean_object* x_161; 
lean_dec(x_155);
if (lean_is_scalar(x_156)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_156;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_158);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_137);
x_162 = lean_ctor_get(x_154, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_163 = x_154;
} else {
 lean_dec_ref(x_154);
 x_163 = lean_box(0);
}
x_164 = l_Lake_mkExceptionMessage(x_1, x_162);
x_165 = l_Lake_Toml_loadToml___closed__6;
x_166 = l_Lean_MessageLog_add(x_164, x_165);
if (lean_is_scalar(x_163)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_163;
}
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
block_183:
{
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_170 = lean_st_ref_take(x_137);
x_171 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 2);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_170, 3);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_170, 4);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_170, 6);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_170, 7);
lean_inc_ref(x_177);
x_178 = lean_ctor_get(x_170, 8);
lean_inc_ref(x_178);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 lean_ctor_release(x_170, 5);
 lean_ctor_release(x_170, 6);
 lean_ctor_release(x_170, 7);
 lean_ctor_release(x_170, 8);
 x_179 = x_170;
} else {
 lean_dec_ref(x_170);
 x_179 = lean_box(0);
}
x_180 = l_Lean_Kernel_enableDiag(x_171, x_148);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 9, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_172);
lean_ctor_set(x_181, 2, x_173);
lean_ctor_set(x_181, 3, x_174);
lean_ctor_set(x_181, 4, x_175);
lean_ctor_set(x_181, 5, x_132);
lean_ctor_set(x_181, 6, x_176);
lean_ctor_set(x_181, 7, x_177);
lean_ctor_set(x_181, 8, x_178);
x_182 = lean_st_ref_set(x_137, x_181);
lean_inc(x_137);
x_149 = x_137;
x_150 = lean_box(0);
goto block_168;
}
else
{
lean_inc(x_137);
x_149 = x_137;
x_150 = lean_box(0);
goto block_168;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_103);
x_185 = lean_ctor_get(x_115, 0);
lean_inc(x_185);
lean_dec_ref(x_115);
x_186 = l_Lake_mkParserErrorMessage(x_1, x_114, x_185);
lean_dec_ref(x_114);
x_187 = l_Lake_Toml_loadToml___closed__6;
x_188 = l_Lean_MessageLog_add(x_186, x_187);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_4);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_191 = lean_ctor_get(x_4, 0);
x_192 = l_Lake_Toml_loadToml___closed__28;
x_193 = lean_io_error_to_string(x_191);
x_194 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Lean_MessageData_ofFormat(x_194);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_192);
lean_ctor_set(x_196, 1, x_195);
x_197 = 2;
x_198 = l_Lake_mkMessageNoPos(x_1, x_196, x_197);
x_199 = l_Lake_Toml_loadToml___closed__6;
x_200 = l_Lean_MessageLog_add(x_198, x_199);
lean_ctor_set(x_4, 0, x_200);
return x_4;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_201 = lean_ctor_get(x_4, 0);
lean_inc(x_201);
lean_dec(x_4);
x_202 = l_Lake_Toml_loadToml___closed__28;
x_203 = lean_io_error_to_string(x_201);
x_204 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = l_Lean_MessageData_ofFormat(x_204);
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_202);
lean_ctor_set(x_206, 1, x_205);
x_207 = 2;
x_208 = l_Lake_mkMessageNoPos(x_1, x_206, x_207);
x_209 = l_Lake_Toml_loadToml___closed__6;
x_210 = l_Lean_MessageLog_add(x_208, x_209);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
return x_211;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_loadToml(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* initialize_Lean_Parser(uint8_t builtin);
lean_object* initialize_Lake_Toml_Elab(uint8_t builtin);
lean_object* initialize_Lake_Util_Message(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Load(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Message(builtin);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
