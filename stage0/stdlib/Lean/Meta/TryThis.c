// Lean compiler output
// Module: Lean.Meta.TryThis
// Imports: Lean.CoreM Lean.Message Lean.Elab.InfoTree.Types Lean.Data.Lsp.Basic Lean.PrettyPrinter
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
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3;
static uint8_t l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__18;
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion___closed__1;
double lean_float_mul(double, double);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6;
static lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__5;
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success;
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__4;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instSuggestionStyleInhabited;
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedJson;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_format_inputWidth;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3;
static lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8;
static lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__5;
static lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__6;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__20;
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lambda__1___boxed(lean_object*);
lean_object* l_String_findLineStart(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4;
double lean_float_add(double, double);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10;
extern lean_object* l_Lean_instToJsonJson;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_processSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__23;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_processSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__16;
double pow(double, double);
static lean_object* l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___boxed(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__18;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__26;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__5;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(uint8_t);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__22;
lean_object* l_String_findAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__25;
lean_object* lean_float_to_string(double);
static lean_object* l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__4;
static lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16;
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lambda__1(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(double, uint8_t);
lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__15;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instSuggestionStyleToJson;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__21;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_float_decLe(double, double);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth___boxed(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49_;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__14;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
double round(double);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__14;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_5____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__24;
static lean_object* l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__6;
static lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17;
double lean_float_sub(double, double);
static lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13;
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("TryThis", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("TryThisInfo", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__2;
x_3 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__4;
x_5 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__5;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49_;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestionText(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_MessageData_ofSyntax(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
lean_ctor_set_tag(x_1, 3);
x_5 = l_Lean_MessageData_ofFormat(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofFormat(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeHeadTSyntaxConsSyntaxNodeKindNilSuggestionText(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeStringSuggestionText(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instSuggestionStyleInhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedJson;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instSuggestionStyleToJson() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToJsonJson;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pointer dim", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("className", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("var(--vscode-errorForeground)", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("color", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9;
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("style", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14;
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("underline wavy var(--vscode-editorError-foreground) 1pt", 55, 55);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("textDecoration", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__18;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__21;
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__22;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__25;
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__26;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gold pointer dim", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4;
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("underline wavy var(--vscode-editorWarning-foreground) 1pt", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__18;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9;
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13;
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__14;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("information pointer dim", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4;
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("goal-hyp pointer dim", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4;
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("goal-inaccessible pointer dim", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4;
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__5;
return x_1;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(120u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(60u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static double _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(75u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hsl(", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" 95% ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("%)", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Apply suggestion", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("title", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Apply suggestion (", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__18() {
_start:
{
double x_1; double x_2; uint8_t x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2;
x_3 = lean_float_decLe(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(double x_1, uint8_t x_2) {
_start:
{
double x_3; uint8_t x_4; lean_object* x_5; double x_6; 
x_3 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1;
x_4 = lean_float_decLe(x_1, x_3);
x_5 = lean_box(0);
if (x_4 == 0)
{
double x_53; uint8_t x_54; 
x_53 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2;
x_54 = lean_float_decLe(x_1, x_53);
if (x_54 == 0)
{
x_6 = x_53;
goto block_52;
}
else
{
x_6 = x_1;
goto block_52;
}
}
else
{
uint8_t x_55; 
x_55 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__18;
if (x_55 == 0)
{
double x_56; 
x_56 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2;
x_6 = x_56;
goto block_52;
}
else
{
x_6 = x_3;
goto block_52;
}
}
block_52:
{
double x_7; double x_8; double x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; double x_15; double x_16; double x_17; double x_18; double x_19; double x_20; double x_21; double x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_7 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3;
x_8 = lean_float_mul(x_6, x_7);
x_9 = round(x_8);
x_10 = lean_float_to_string(x_9);
x_11 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5;
x_16 = lean_float_sub(x_6, x_15);
x_17 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6;
x_18 = pow(x_16, x_17);
x_19 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7;
x_20 = lean_float_add(x_18, x_19);
x_21 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4;
x_22 = lean_float_mul(x_21, x_20);
x_23 = lean_float_to_string(x_22);
x_24 = lean_string_append(x_14, x_23);
lean_dec(x_23);
x_25 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
x_31 = l_Lean_Json_mkObj(x_30);
x_32 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
if (x_2 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__15;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Json_mkObj(x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_39 = lean_float_to_string(x_6);
x_40 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__16;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__17;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_5);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Json_mkObj(x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_float(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText___closed__1;
x_3 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instToMessageDataSuggestion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_MessageData_ofSyntax(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_ctor_set_tag(x_3, 3);
x_7 = l_Lean_MessageData_ofFormat(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_MessageData_ofFormat(x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_instCoeSuggestionTextSuggestion(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lambda__1(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = 32;
x_3 = lean_uint32_dec_eq(x_1, x_2);
x_4 = l_instDecidableNot___rarg(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_4);
x_5 = l_String_findLineStart(x_3, x_4);
x_6 = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___closed__1;
lean_inc(x_5);
x_7 = l_String_findAux(x_3, x_6, x_4, x_5);
x_8 = lean_nat_sub(x_7, x_5);
lean_dec(x_7);
x_9 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("format", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inputWidth", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ideal input width", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(100u);
x_2 = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__4;
x_3 = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__2;
x_3 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__4;
x_5 = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__1;
x_6 = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__2;
x_7 = l_Lean_Name_mkStr6(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__3;
x_3 = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__6;
x_4 = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__7;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_getInputWidth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Tactic_TryThis_getInputWidth___closed__1;
x_3 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_getInputWidth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Tactic_TryThis_getInputWidth(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_pretty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_ppCategory(x_5, x_6, x_2, x_3, x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_ctor_set_tag(x_1, 3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_ppCategory(x_1, x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_format_pretty(x_11, x_5, x_3, x_4);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_format_pretty(x_13, x_5, x_3, x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = l_Lean_Meta_Tactic_TryThis_getInputWidth___closed__1;
x_12 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra___lambda__1(x_8, x_9, x_3, x_4, x_12, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra___lambda__1(x_14, x_15, x_3, x_4, x_16, x_5, x_6, x_7);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Json_mkObj(x_3);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_2);
x_16 = lean_apply_1(x_15, x_2);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
lean_inc(x_2);
x_21 = lean_apply_1(x_20, x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_box(0);
x_16 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__1(x_1, x_2, x_14, x_15, x_5, x_6, x_7);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("postInfo", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__2(x_1, x_2, x_3, x_9, x_5, x_6, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_ctor_set_tag(x_8, 3);
x_12 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_box(0);
x_16 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__2(x_1, x_2, x_14, x_15, x_5, x_6, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__2(x_1, x_2, x_21, x_22, x_5, x_6, x_7);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("suggestion", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("preInfo", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3(x_1, x_10, x_16, x_18, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_ctor_set_tag(x_17, 3);
x_21 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__2;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3(x_1, x_10, x_23, x_24, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__2;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_16);
x_31 = lean_box(0);
x_32 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3(x_1, x_10, x_30, x_31, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_uget(x_5, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_5, x_4, x_12);
x_14 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM(x_11, x_14, x_1, x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_20 = lean_array_uset(x_13, x_4, x_16);
x_4 = x_19;
x_5 = x_20;
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_processSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_2);
x_9 = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(x_8, x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_array_size(x_3);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__1(x_11, x_12, x_13, x_14, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_array_size(x_17);
lean_inc(x_17);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__2(x_18, x_14, x_17);
x_20 = 0;
x_21 = l_Lean_Syntax_getRange_x3f(x_1, x_20);
x_22 = l_Lean_FileMap_utf8RangeToLspRange(x_8, x_2);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_4);
x_24 = l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo;
lean_ctor_set(x_9, 1, x_23);
lean_ctor_set(x_9, 0, x_24);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = 1;
x_26 = l_Lean_Syntax_ofRange(x_2, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
x_28 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = 1;
x_33 = l_Lean_Syntax_ofRange(x_31, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_9);
lean_ctor_set_tag(x_21, 9);
lean_ctor_set(x_21, 0, x_34);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_21);
lean_ctor_set(x_35, 2, x_22);
lean_ctor_set(x_15, 0, x_35);
return x_15;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
lean_dec(x_21);
x_37 = 1;
x_38 = l_Lean_Syntax_ofRange(x_36, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
x_40 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_17);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_22);
lean_ctor_set(x_15, 0, x_41);
return x_15;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
x_44 = lean_array_size(x_42);
lean_inc(x_42);
x_45 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__2(x_44, x_14, x_42);
x_46 = 0;
x_47 = l_Lean_Syntax_getRange_x3f(x_1, x_46);
x_48 = l_Lean_FileMap_utf8RangeToLspRange(x_8, x_2);
lean_inc(x_48);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_4);
x_50 = l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo;
lean_ctor_set(x_9, 1, x_49);
lean_ctor_set(x_9, 0, x_50);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = 1;
x_52 = l_Lean_Syntax_ofRange(x_2, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_9);
x_54 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_43);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_2);
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_58 = x_47;
} else {
 lean_dec_ref(x_47);
 x_58 = lean_box(0);
}
x_59 = 1;
x_60 = l_Lean_Syntax_ofRange(x_57, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_9);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(9, 1, 0);
} else {
 x_62 = x_58;
 lean_ctor_set_tag(x_62, 9);
}
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_42);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_48);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_43);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_free_object(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_15);
if (x_65 == 0)
{
return x_15;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_15, 0);
x_67 = lean_ctor_get(x_15, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_15);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_71 = lean_array_size(x_3);
x_72 = 0;
x_73 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__1(x_69, x_70, x_71, x_72, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_array_size(x_74);
lean_inc(x_74);
x_78 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__2(x_77, x_72, x_74);
x_79 = 0;
x_80 = l_Lean_Syntax_getRange_x3f(x_1, x_79);
x_81 = l_Lean_FileMap_utf8RangeToLspRange(x_8, x_2);
lean_inc(x_81);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_4);
x_83 = l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo;
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = 1;
x_86 = l_Lean_Syntax_ofRange(x_2, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
x_88 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_81);
if (lean_is_scalar(x_76)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_76;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_75);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_2);
x_91 = lean_ctor_get(x_80, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_92 = x_80;
} else {
 lean_dec_ref(x_80);
 x_92 = lean_box(0);
}
x_93 = 1;
x_94 = l_Lean_Syntax_ofRange(x_91, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_84);
if (lean_is_scalar(x_92)) {
 x_96 = lean_alloc_ctor(9, 1, 0);
} else {
 x_96 = x_92;
 lean_ctor_set_tag(x_96, 9);
}
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_74);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_81);
if (lean_is_scalar(x_76)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_76;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_75);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_99 = lean_ctor_get(x_73, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_73, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_101 = x_73;
} else {
 lean_dec_ref(x_73);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__1(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_processSuggestions___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_processSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_TryThis_processSuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_InfoTree_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_TryThis(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__1 = _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__1);
l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__2 = _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__2);
l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__3 = _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__3);
l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__4 = _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__4);
l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__5 = _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__5);
l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__6 = _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__6();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49____closed__6);
l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49_ = _init_l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49_();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instImpl____x40_Lean_Meta_TryThis___hyg_49_);
l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo = _init_l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo);
l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText___closed__1);
l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText = _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestionText);
l_Lean_Meta_Tactic_TryThis_instSuggestionStyleInhabited = _init_l_Lean_Meta_Tactic_TryThis_instSuggestionStyleInhabited();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instSuggestionStyleInhabited);
l_Lean_Meta_Tactic_TryThis_instSuggestionStyleToJson = _init_l_Lean_Meta_Tactic_TryThis_instSuggestionStyleToJson();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instSuggestionStyleToJson);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__1);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__2);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__3);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__4);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__5);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__6);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__7);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__8);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__9);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__10);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__11);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__12);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__13);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__14);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__15);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__16);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__17);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__18 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__18();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__18);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__19 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__19();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__19);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__20 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__20();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__20);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__21 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__21();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__21);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__22 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__22();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__22);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__23 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__23();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__23);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__24 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__24();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__24);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__25 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__25();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__25);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__26 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__26();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_error___closed__26);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__1);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__2);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__3);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__4);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__5);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__6);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__7);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__8);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__9);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__10);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__11);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__12);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__13);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__14 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__14();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_warning___closed__14);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__1);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__2);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__3);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__4);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__5 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success___closed__5);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_success);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__1);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__2);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__3);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__4);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__5 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis___closed__5);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asHypothesis);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__1);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__2);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__3);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__4);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__5 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible___closed__5);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_asInaccessible);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__1();
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__2();
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__3();
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__4();
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__5();
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__6();
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__7();
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__8);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__9);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__10);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__11);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__12);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__13);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__14 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__14();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__14);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__15 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__15();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__15);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__16 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__16();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__16);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__17 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__17();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__17);
l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__18 = _init_l_Lean_Meta_Tactic_TryThis_SuggestionStyle_value___closed__18();
l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion___closed__1);
l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion = _init_l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion);
l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_getIndentAndColumn___closed__1);
l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__1 = _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__1);
l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__2 = _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__2);
l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__3 = _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__3);
l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__4 = _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__4);
l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__5 = _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__5);
l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__6 = _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__6();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__6);
l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__7 = _init_l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__7();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707____closed__7);
if (builtin) {res = l_Lean_Meta_Tactic_TryThis_initFn____x40_Lean_Meta_TryThis___hyg_707_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_TryThis_format_inputWidth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_format_inputWidth);
lean_dec_ref(res);
}l_Lean_Meta_Tactic_TryThis_getInputWidth___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_getInputWidth___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_getInputWidth___closed__1);
l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___lambda__3___closed__1);
l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__1);
l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_Suggestion_toJsonAndInfoM___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
