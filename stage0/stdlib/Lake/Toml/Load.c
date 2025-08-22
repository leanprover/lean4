// Lean compiler output
// Module: Lake.Toml.Load
// Imports: Lake.Toml.Elab Lake.Util.Message
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
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_PrettyPrinter_format_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__24;
static lean_object* l_Lake_Toml_loadToml___closed__16;
static lean_object* l_Lake_Toml_loadToml___closed__13;
static lean_object* l_Lake_Toml_loadToml___closed__20;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__3;
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lake_Toml_toml;
static uint8_t l_Lake_Toml_loadToml___closed__21;
static lean_object* l_Lake_Toml_loadToml___closed__14;
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__11;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__1;
static lean_object* l_Lake_Toml_loadToml___closed__26;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__8;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__22;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__2;
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
static lean_object* l_Lake_Toml_loadToml___closed__15;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lake_Toml_loadToml___closed__23;
uint8_t l_Lean_Option_get___at___Lean_logAt___at___Lean_logWarningAt___at_____private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn____x40_Lean_Parser_Tactic_Doc___hyg_811__spec__2_spec__2_spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__6;
static lean_object* l_Lake_Toml_loadToml___closed__5;
static lean_object* l_Lake_Toml_loadToml___closed__4;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__9;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__10;
static lean_object* l_Lake_Toml_loadToml___closed__0;
static lean_object* l_Lake_Toml_loadToml___closed__7;
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__19;
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
static lean_object* l_Lake_Toml_loadToml___closed__25;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
static lean_object* _init_l_Lake_Toml_loadToml___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Data_Trie_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("end of input", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_loadToml___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_loadToml___closed__3;
x_2 = l_Lake_Toml_loadToml___closed__1;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lake_Toml_loadToml___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__8() {
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
static lean_object* _init_l_Lake_Toml_loadToml___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Toml_loadToml___closed__9;
x_4 = l_Lake_Toml_loadToml___closed__10;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__12() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__14;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lake_Toml_loadToml___closed__11;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lake_Toml_loadToml___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_Toml_loadToml___closed__20;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at___Lean_logAt___at___Lean_logWarningAt___at_____private_Lean_Parser_Tactic_Doc_0__Lean_Parser_Tactic_Doc_initFn____x40_Lean_Parser_Tactic_Doc___hyg_811__spec__2_spec__2_spec__2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_loadToml___closed__22;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at___Lean_PrettyPrinter_format_spec__1(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to initialize TOML environment: ", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__24;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_loadToml___closed__1;
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
x_8 = l_Lake_Toml_toml;
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
x_16 = l_Lake_Toml_loadToml___closed__0;
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
x_22 = lean_string_utf8_at_end(x_10, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_20);
lean_dec(x_6);
x_23 = l_Lake_Toml_loadToml___closed__4;
x_24 = l_Lake_mkParserErrorMessage(x_1, x_18, x_23);
lean_dec_ref(x_18);
x_25 = l_Lean_MessageLog_empty;
x_26 = l_Lean_MessageLog_add(x_24, x_25);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_26);
return x_4;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_87; uint8_t x_110; 
lean_dec_ref(x_18);
lean_free_object(x_4);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_unsigned_to_nat(2u);
x_30 = l_Lake_Toml_loadToml___closed__7;
x_31 = l_Lake_Toml_loadToml___closed__8;
x_32 = l_Lake_Toml_loadToml___closed__11;
x_33 = l_Lake_Toml_loadToml___closed__12;
x_34 = l_Lake_Toml_loadToml___closed__14;
x_35 = l_Lake_Toml_loadToml___closed__15;
x_36 = l_Lake_Toml_loadToml___closed__16;
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_22);
x_38 = l_Lake_Toml_loadToml___closed__17;
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
x_43 = l_Lake_Toml_loadToml___closed__18;
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
x_53 = l_Lake_Toml_loadToml___closed__19;
x_54 = 0;
x_55 = lean_box(0);
x_56 = l_Lake_Toml_loadToml___closed__21;
x_110 = l_Lean_Kernel_isDiagnosticsEnabled(x_50);
lean_dec_ref(x_50);
if (x_110 == 0)
{
if (x_56 == 0)
{
x_87 = x_22;
goto block_109;
}
else
{
x_87 = x_110;
goto block_109;
}
}
else
{
x_87 = x_56;
goto block_109;
}
block_86:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l_Lake_Toml_loadToml___closed__23;
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_60 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_60, 0, x_11);
lean_ctor_set(x_60, 1, x_12);
lean_ctor_set(x_60, 2, x_13);
lean_ctor_set(x_60, 3, x_27);
lean_ctor_set(x_60, 4, x_59);
lean_ctor_set(x_60, 5, x_52);
lean_ctor_set(x_60, 6, x_14);
lean_ctor_set(x_60, 7, x_13);
lean_ctor_set(x_60, 8, x_27);
lean_ctor_set(x_60, 9, x_53);
lean_ctor_set(x_60, 10, x_14);
lean_ctor_set(x_60, 11, x_28);
lean_ctor_set(x_60, 12, x_55);
lean_ctor_set(x_60, 13, x_45);
lean_ctor_set_uint8(x_60, sizeof(void*)*14, x_56);
lean_ctor_set_uint8(x_60, sizeof(void*)*14 + 1, x_54);
x_61 = l_Lake_Toml_elabToml(x_51, x_60, x_57, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec_ref(x_1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_st_ref_get(x_41, x_63);
lean_dec(x_41);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_66, 6);
lean_inc_ref(x_67);
lean_dec(x_66);
x_68 = l_Lean_MessageLog_hasErrors(x_67);
if (x_68 == 0)
{
lean_dec_ref(x_67);
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
else
{
lean_dec(x_62);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
x_71 = lean_ctor_get(x_69, 6);
lean_inc_ref(x_71);
lean_dec(x_69);
x_72 = l_Lean_MessageLog_hasErrors(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec_ref(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_62);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_41);
x_75 = !lean_is_exclusive(x_61);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_61, 0);
x_77 = l_Lake_mkExceptionMessage(x_1, x_76);
x_78 = l_Lean_MessageLog_empty;
x_79 = l_Lean_MessageLog_add(x_77, x_78);
lean_ctor_set(x_61, 0, x_79);
return x_61;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_61, 0);
x_81 = lean_ctor_get(x_61, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_61);
x_82 = l_Lake_mkExceptionMessage(x_1, x_80);
x_83 = l_Lean_MessageLog_empty;
x_84 = l_Lean_MessageLog_add(x_82, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
}
block_109:
{
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_st_ref_take(x_41, x_49);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec_ref(x_88);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_89, 0);
x_93 = lean_ctor_get(x_89, 5);
lean_dec(x_93);
x_94 = l_Lean_Kernel_enableDiag(x_92, x_56);
lean_ctor_set(x_89, 5, x_35);
lean_ctor_set(x_89, 0, x_94);
x_95 = lean_st_ref_set(x_41, x_89, x_90);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
lean_inc(x_41);
x_57 = x_41;
x_58 = x_96;
goto block_86;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_97 = lean_ctor_get(x_89, 0);
x_98 = lean_ctor_get(x_89, 1);
x_99 = lean_ctor_get(x_89, 2);
x_100 = lean_ctor_get(x_89, 3);
x_101 = lean_ctor_get(x_89, 4);
x_102 = lean_ctor_get(x_89, 6);
x_103 = lean_ctor_get(x_89, 7);
x_104 = lean_ctor_get(x_89, 8);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_89);
x_105 = l_Lean_Kernel_enableDiag(x_97, x_56);
x_106 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_98);
lean_ctor_set(x_106, 2, x_99);
lean_ctor_set(x_106, 3, x_100);
lean_ctor_set(x_106, 4, x_101);
lean_ctor_set(x_106, 5, x_35);
lean_ctor_set(x_106, 6, x_102);
lean_ctor_set(x_106, 7, x_103);
lean_ctor_set(x_106, 8, x_104);
x_107 = lean_st_ref_set(x_41, x_106, x_90);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec_ref(x_107);
lean_inc(x_41);
x_57 = x_41;
x_58 = x_108;
goto block_86;
}
}
else
{
lean_inc(x_41);
x_57 = x_41;
x_58 = x_49;
goto block_86;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_6);
x_111 = lean_ctor_get(x_19, 0);
lean_inc(x_111);
lean_dec_ref(x_19);
x_112 = l_Lake_mkParserErrorMessage(x_1, x_18, x_111);
lean_dec_ref(x_18);
x_113 = l_Lean_MessageLog_empty;
x_114 = l_Lean_MessageLog_add(x_112, x_113);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_114);
return x_4;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_115 = lean_ctor_get(x_4, 0);
x_116 = lean_ctor_get(x_4, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_4);
x_117 = l_Lake_Toml_toml;
x_118 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_1, 0);
x_120 = lean_ctor_get(x_1, 1);
x_121 = lean_ctor_get(x_1, 2);
x_122 = lean_box(0);
x_123 = lean_box(0);
lean_inc(x_115);
x_124 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_124, 0, x_115);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_122);
x_125 = l_Lake_Toml_loadToml___closed__0;
x_126 = l_Lean_Parser_mkParserState(x_119);
lean_inc_ref(x_1);
x_127 = l_Lean_Parser_ParserFn_run(x_118, x_1, x_124, x_125, x_126);
x_128 = lean_ctor_get(x_127, 4);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_127, 2);
lean_inc(x_130);
x_131 = lean_string_utf8_at_end(x_119, x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_129);
lean_dec(x_115);
x_132 = l_Lake_Toml_loadToml___closed__4;
x_133 = l_Lake_mkParserErrorMessage(x_1, x_127, x_132);
lean_dec_ref(x_127);
x_134 = l_Lean_MessageLog_empty;
x_135 = l_Lean_MessageLog_add(x_133, x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_116);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; uint8_t x_190; uint8_t x_208; 
lean_dec_ref(x_127);
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_unsigned_to_nat(2u);
x_140 = l_Lake_Toml_loadToml___closed__7;
x_141 = l_Lake_Toml_loadToml___closed__8;
x_142 = l_Lake_Toml_loadToml___closed__11;
x_143 = l_Lake_Toml_loadToml___closed__12;
x_144 = l_Lake_Toml_loadToml___closed__14;
x_145 = l_Lake_Toml_loadToml___closed__15;
x_146 = l_Lake_Toml_loadToml___closed__16;
x_147 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_144);
lean_ctor_set(x_147, 2, x_142);
lean_ctor_set_uint8(x_147, sizeof(void*)*3, x_131);
x_148 = l_Lake_Toml_loadToml___closed__17;
x_149 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_149, 0, x_115);
lean_ctor_set(x_149, 1, x_139);
lean_ctor_set(x_149, 2, x_140);
lean_ctor_set(x_149, 3, x_141);
lean_ctor_set(x_149, 4, x_143);
lean_ctor_set(x_149, 5, x_145);
lean_ctor_set(x_149, 6, x_146);
lean_ctor_set(x_149, 7, x_147);
lean_ctor_set(x_149, 8, x_148);
x_150 = lean_st_mk_ref(x_149, x_116);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec_ref(x_150);
x_153 = l_Lake_Toml_loadToml___closed__18;
x_154 = lean_st_ref_get(x_153, x_152);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec_ref(x_154);
x_157 = lean_st_ref_get(x_151, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec_ref(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc_ref(x_160);
lean_dec(x_158);
x_161 = l_Lean_Parser_SyntaxStack_back(x_129);
lean_dec_ref(x_129);
x_162 = lean_box(0);
x_163 = l_Lake_Toml_loadToml___closed__19;
x_164 = 0;
x_165 = lean_box(0);
x_166 = l_Lake_Toml_loadToml___closed__21;
x_208 = l_Lean_Kernel_isDiagnosticsEnabled(x_160);
lean_dec_ref(x_160);
if (x_208 == 0)
{
if (x_166 == 0)
{
x_190 = x_131;
goto block_207;
}
else
{
x_190 = x_208;
goto block_207;
}
}
else
{
x_190 = x_166;
goto block_207;
}
block_189:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = l_Lake_Toml_loadToml___closed__23;
lean_inc_ref(x_121);
lean_inc_ref(x_120);
x_170 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_170, 0, x_120);
lean_ctor_set(x_170, 1, x_121);
lean_ctor_set(x_170, 2, x_122);
lean_ctor_set(x_170, 3, x_137);
lean_ctor_set(x_170, 4, x_169);
lean_ctor_set(x_170, 5, x_162);
lean_ctor_set(x_170, 6, x_123);
lean_ctor_set(x_170, 7, x_122);
lean_ctor_set(x_170, 8, x_137);
lean_ctor_set(x_170, 9, x_163);
lean_ctor_set(x_170, 10, x_123);
lean_ctor_set(x_170, 11, x_138);
lean_ctor_set(x_170, 12, x_165);
lean_ctor_set(x_170, 13, x_155);
lean_ctor_set_uint8(x_170, sizeof(void*)*14, x_166);
lean_ctor_set_uint8(x_170, sizeof(void*)*14 + 1, x_164);
x_171 = l_Lake_Toml_elabToml(x_161, x_170, x_167, x_168);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
lean_dec_ref(x_1);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec_ref(x_171);
x_174 = lean_st_ref_get(x_151, x_173);
lean_dec(x_151);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_175, 6);
lean_inc_ref(x_178);
lean_dec(x_175);
x_179 = l_Lean_MessageLog_hasErrors(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
lean_dec_ref(x_178);
if (lean_is_scalar(x_177)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_177;
}
lean_ctor_set(x_180, 0, x_172);
lean_ctor_set(x_180, 1, x_176);
return x_180;
}
else
{
lean_object* x_181; 
lean_dec(x_172);
if (lean_is_scalar(x_177)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_177;
 lean_ctor_set_tag(x_181, 1);
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_176);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_151);
x_182 = lean_ctor_get(x_171, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_171, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_184 = x_171;
} else {
 lean_dec_ref(x_171);
 x_184 = lean_box(0);
}
x_185 = l_Lake_mkExceptionMessage(x_1, x_182);
x_186 = l_Lean_MessageLog_empty;
x_187 = l_Lean_MessageLog_add(x_185, x_186);
if (lean_is_scalar(x_184)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_184;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_183);
return x_188;
}
}
block_207:
{
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_191 = lean_st_ref_take(x_151, x_159);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec_ref(x_191);
x_194 = lean_ctor_get(x_192, 0);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 2);
lean_inc_ref(x_196);
x_197 = lean_ctor_get(x_192, 3);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_192, 4);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_192, 6);
lean_inc_ref(x_199);
x_200 = lean_ctor_get(x_192, 7);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_192, 8);
lean_inc_ref(x_201);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 lean_ctor_release(x_192, 6);
 lean_ctor_release(x_192, 7);
 lean_ctor_release(x_192, 8);
 x_202 = x_192;
} else {
 lean_dec_ref(x_192);
 x_202 = lean_box(0);
}
x_203 = l_Lean_Kernel_enableDiag(x_194, x_166);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 9, 0);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_195);
lean_ctor_set(x_204, 2, x_196);
lean_ctor_set(x_204, 3, x_197);
lean_ctor_set(x_204, 4, x_198);
lean_ctor_set(x_204, 5, x_145);
lean_ctor_set(x_204, 6, x_199);
lean_ctor_set(x_204, 7, x_200);
lean_ctor_set(x_204, 8, x_201);
x_205 = lean_st_ref_set(x_151, x_204, x_193);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec_ref(x_205);
lean_inc(x_151);
x_167 = x_151;
x_168 = x_206;
goto block_189;
}
else
{
lean_inc(x_151);
x_167 = x_151;
x_168 = x_159;
goto block_189;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_115);
x_209 = lean_ctor_get(x_128, 0);
lean_inc(x_209);
lean_dec_ref(x_128);
x_210 = l_Lake_mkParserErrorMessage(x_1, x_127, x_209);
lean_dec_ref(x_127);
x_211 = l_Lean_MessageLog_empty;
x_212 = l_Lean_MessageLog_add(x_210, x_211);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_116);
return x_213;
}
}
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_4);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_215 = lean_ctor_get(x_4, 0);
x_216 = l_Lake_Toml_loadToml___closed__25;
x_217 = lean_io_error_to_string(x_215);
x_218 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_218, 0, x_217);
x_219 = l_Lean_MessageData_ofFormat(x_218);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_216);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lake_Toml_loadToml___closed__26;
x_222 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = 2;
x_224 = l_Lake_mkMessageNoPos(x_1, x_222, x_223);
x_225 = l_Lean_MessageLog_empty;
x_226 = l_Lean_MessageLog_add(x_224, x_225);
lean_ctor_set(x_4, 0, x_226);
return x_4;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_227 = lean_ctor_get(x_4, 0);
x_228 = lean_ctor_get(x_4, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_4);
x_229 = l_Lake_Toml_loadToml___closed__25;
x_230 = lean_io_error_to_string(x_227);
x_231 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_232 = l_Lean_MessageData_ofFormat(x_231);
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_229);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Lake_Toml_loadToml___closed__26;
x_235 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = 2;
x_237 = l_Lake_mkMessageNoPos(x_1, x_235, x_236);
x_238 = l_Lean_MessageLog_empty;
x_239 = l_Lean_MessageLog_add(x_237, x_238);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_228);
return x_240;
}
}
}
}
lean_object* initialize_Lake_Toml_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Load(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
