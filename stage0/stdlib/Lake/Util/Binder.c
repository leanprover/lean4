// Lean compiler output
// Module: Lake.Util.Binder
// Imports: Init Lean.Parser.Term Lean.Elab.Term Lean.Expr
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
lean_object* l_Lean_Macro_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinders___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderType___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__13;
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__6;
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeBinderTSyntaxConsSyntaxNodeKindIdentKindMkStr4Nil___boxed(lean_object*);
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_binder_formatter___closed__1;
LEAN_EXPORT lean_object* l_Lake_instCoeHoleBinderIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeNamedArgumentArgument___boxed(lean_object*);
lean_object* l_Lean_Parser_Term_bracketedBinder_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_instCoeHoleTerm(lean_object*);
static lean_object* l_Lake_binder_parenthesizer___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_binder_parenthesizer___closed__1;
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
static lean_object* l_Lake_mkHoleFrom___closed__6;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lake_matchBinder___closed__8;
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__3;
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__9;
static lean_object* l_Lake_matchBinder___closed__7;
static lean_object* l_Lake_mkHoleFrom___closed__5;
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_binder_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_matchBinder(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_binder___closed__2;
static lean_object* l_Lake_BinderSyntaxView_mkArgument___closed__2;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeHoleBinderIdent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeNamedArgumentArgument(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentFunBinder(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__1;
lean_object* l_Lean_Parser_Term_binderIdent_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BinderSyntaxView_mkArgument___closed__1;
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__11;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_matchBinder___closed__5;
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentFunBinder___boxed(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instCoeIdentBinderIdent(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_expandOptType(lean_object*, lean_object*);
static lean_object* l_Lake_matchBinder___closed__6;
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_binderIdent_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeHoleTerm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument___boxed(lean_object*);
static lean_object* l_Lake_mkHoleFrom___closed__7;
extern lean_object* l_Lean_Parser_Term_binderIdent;
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandOptType___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_matchBinder___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_expandBinderIdent___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkHoleFrom___closed__1;
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom___boxed(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandOptIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeEllipsisArgument___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_BinderSyntaxView_mkArgument___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBinderIds(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_binder___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinderType(lean_object*, lean_object*);
static lean_object* l_Lake_matchBinder___closed__3;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_binder_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_expandBinders(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkHoleFrom___closed__3;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__3;
static lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__2;
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__1;
LEAN_EXPORT lean_object* l_Lake_expandOptIdent___boxed(lean_object*);
static lean_object* l_Lake_binder_formatter___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__5;
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom(lean_object*);
static lean_object* l_Lake_matchBinder___closed__4;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_mkArray1___rarg(lean_object*);
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__12;
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument(lean_object*);
static lean_object* l_Lake_BinderSyntaxView_mkBinder___closed__10;
LEAN_EXPORT lean_object* l_Lake_getBinderIds___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeEllipsisArgument(lean_object*);
lean_object* l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_expandBinderIdent___spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_matchBinder___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_binder;
static lean_object* l_Lake_mkHoleFrom___closed__4;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeIdentBinderIdent___boxed(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_mkHoleFrom___closed__2;
lean_object* l_Lean_Parser_Term_bracketedBinder(uint8_t);
LEAN_EXPORT lean_object* l_Lake_instCoeBinderTSyntaxConsSyntaxNodeKindIdentKindMkStr4Nil(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_modifier_x3f___default;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_expandBinders___closed__1;
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTermArgument___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeTermArgument(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeEllipsisArgument(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeEllipsisArgument___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeEllipsisArgument(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeNamedArgumentArgument(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeNamedArgumentArgument___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeNamedArgumentArgument(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mkHoleFrom___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_mkHoleFrom___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_mkHoleFrom___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_mkHoleFrom___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hole", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_mkHoleFrom___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_mkHoleFrom___closed__1;
x_2 = l_Lake_mkHoleFrom___closed__2;
x_3 = l_Lake_mkHoleFrom___closed__3;
x_4 = l_Lake_mkHoleFrom___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_mkHoleFrom___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_mkHoleFrom___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Lake_mkHoleFrom___closed__6;
x_3 = 0;
x_4 = l_Lean_mkAtomFrom(x_1, x_2, x_3);
x_5 = l_Lake_mkHoleFrom___closed__7;
x_6 = lean_array_push(x_5, x_4);
x_7 = lean_box(2);
x_8 = l_Lake_mkHoleFrom___closed__5;
x_9 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_mkHoleFrom___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_mkHoleFrom(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeHoleTerm(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeHoleTerm___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeHoleTerm(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeHoleBinderIdent(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeHoleBinderIdent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeHoleBinderIdent(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeIdentBinderIdent(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeIdentBinderIdent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeIdentBinderIdent(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentFunBinder(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeBinderIdentFunBinder___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeBinderIdentFunBinder(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_binder_formatter___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_Term_bracketedBinder_formatter___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_binder_formatter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_formatter), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_binder_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lake_binder_formatter___closed__2;
x_7 = l_Lake_binder_formatter___closed__1;
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lake_binder_parenthesizer___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_Term_bracketedBinder_parenthesizer___boxed), 6, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_binder_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_binderIdent_parenthesizer), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_binder_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lake_binder_parenthesizer___closed__2;
x_7 = l_Lake_binder_parenthesizer___closed__1;
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lake_binder___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Parser_Term_bracketedBinder(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_binder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_binderIdent;
x_2 = l_Lake_binder___closed__1;
x_3 = l_Lean_Parser_orelse(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_binder() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_binder___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeBinderTSyntaxConsSyntaxNodeKindIdentKindMkStr4Nil(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeBinderTSyntaxConsSyntaxNodeKindIdentKindMkStr4Nil___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeBinderTSyntaxConsSyntaxNodeKindIdentKindMkStr4Nil(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_modifier_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptType(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Syntax_isNone(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lake_mkHoleFrom(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_expandOptType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("identifier or `_` expected", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
lean_inc(x_8);
x_11 = l_Lean_Syntax_getKind(x_8);
x_12 = l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__2;
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lake_mkHoleFrom___closed__5;
x_15 = lean_name_eq(x_11, x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_10);
x_16 = l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__3;
x_17 = l_Lean_Macro_throwErrorAt___rarg(x_8, x_16, x_4, x_5);
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_10, x_2, x_8);
x_2 = x_23;
x_3 = x_24;
goto _start;
}
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_dec(x_11);
x_26 = 1;
x_27 = lean_usize_add(x_2, x_26);
x_28 = lean_array_uset(x_10, x_2, x_8);
x_2 = x_27;
x_3 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getBinderIds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_4 = l_Lean_Syntax_getArgs(x_1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1(x_6, x_7, x_4, x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_getBinderIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_getBinderIds(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__2;
x_9 = l_Lean_addMacroScope(x_7, x_8, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_11, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__2;
x_18 = l_Lean_addMacroScope(x_16, x_17, x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_expandBinderIdent___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_mkIdentFrom(x_1, x_7, x_2);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_Lean_mkIdentFrom(x_1, x_9, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lake_mkHoleFrom___closed__5;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_7 = 0;
x_8 = l_Lean_Elab_Term_mkFreshIdent___at_Lake_expandBinderIdent___spec__1(x_1, x_7, x_2, x_3);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at_Lake_expandBinderIdent___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Term_mkFreshIdent___at_Lake_expandBinderIdent___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isNone(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lake_mkHoleFrom(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandOptIdent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_expandOptIdent(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Syntax_getNumArgs(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lake_mkHoleFrom(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_expandBinderType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isNone(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinderModifier___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_expandBinderModifier(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_9 = lean_array_uget(x_4, x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_4, x_3, x_10);
lean_inc(x_5);
lean_inc(x_9);
x_12 = l_Lake_expandBinderIdent(x_9, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lake_expandBinderType(x_9, x_1);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = 2;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_11, x_3, x_18);
x_3 = x_20;
x_4 = x_21;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_9 = lean_array_uget(x_4, x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_4, x_3, x_10);
lean_inc(x_5);
lean_inc(x_9);
x_12 = l_Lake_expandBinderIdent(x_9, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lake_expandBinderType(x_9, x_1);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = 1;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_11, x_3, x_18);
x_3 = x_20;
x_4 = x_21;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_10 = lean_array_uget(x_5, x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_5, x_4, x_11);
lean_inc(x_6);
lean_inc(x_10);
x_13 = l_Lake_expandBinderIdent(x_10, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lake_expandBinderType(x_10, x_1);
lean_dec(x_10);
x_17 = 0;
lean_inc(x_2);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_array_uset(x_12, x_4, x_18);
x_4 = x_20;
x_5 = x_21;
x_7 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Lake_matchBinder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("explicitBinder", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_matchBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_mkHoleFrom___closed__1;
x_2 = l_Lake_mkHoleFrom___closed__2;
x_3 = l_Lake_mkHoleFrom___closed__3;
x_4 = l_Lake_matchBinder___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_matchBinder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("implicitBinder", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_matchBinder___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_mkHoleFrom___closed__1;
x_2 = l_Lake_mkHoleFrom___closed__2;
x_3 = l_Lake_mkHoleFrom___closed__3;
x_4 = l_Lake_matchBinder___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_matchBinder___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("strictImplicitBinder", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_matchBinder___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_mkHoleFrom___closed__1;
x_2 = l_Lake_mkHoleFrom___closed__2;
x_3 = l_Lake_mkHoleFrom___closed__3;
x_4 = l_Lake_matchBinder___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_matchBinder___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instBinder", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_matchBinder___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_mkHoleFrom___closed__1;
x_2 = l_Lake_mkHoleFrom___closed__2;
x_3 = l_Lake_mkHoleFrom___closed__3;
x_4 = l_Lake_matchBinder___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_matchBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Syntax_isIdent(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lake_mkHoleFrom___closed__5;
x_7 = lean_name_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_matchBinder___closed__2;
x_9 = lean_name_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lake_matchBinder___closed__4;
x_11 = lean_name_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lake_matchBinder___closed__6;
x_13 = lean_name_eq(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lake_matchBinder___closed__8;
x_15 = lean_name_eq(x_4, x_14);
lean_dec(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lake_expandOptIdent(x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = l_Lake_expandBinderIdent(x_20, x_2, x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_box(0);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
x_29 = l_Lake_mkHoleFrom___closed__7;
x_30 = lean_array_push(x_29, x_28);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_34);
x_36 = l_Lake_mkHoleFrom___closed__7;
x_37 = lean_array_push(x_36, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_Syntax_getArg(x_1, x_39);
lean_inc(x_2);
x_41 = l_Lake_getBinderIds(x_40, x_2, x_3);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(2u);
x_45 = l_Lean_Syntax_getArg(x_1, x_44);
lean_dec(x_1);
x_46 = lean_array_get_size(x_42);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = 0;
x_49 = l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__1(x_45, x_47, x_48, x_42, x_2, x_43);
lean_dec(x_45);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_41, 0);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_41);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_4);
x_54 = lean_unsigned_to_nat(1u);
x_55 = l_Lean_Syntax_getArg(x_1, x_54);
lean_inc(x_2);
x_56 = l_Lake_getBinderIds(x_55, x_2, x_3);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(2u);
x_60 = l_Lean_Syntax_getArg(x_1, x_59);
lean_dec(x_1);
x_61 = lean_array_get_size(x_57);
x_62 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_63 = 0;
x_64 = l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__2(x_60, x_62, x_63, x_57, x_2, x_58);
lean_dec(x_60);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_56);
if (x_65 == 0)
{
return x_56;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_56, 0);
x_67 = lean_ctor_get(x_56, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_56);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_4);
x_69 = lean_unsigned_to_nat(1u);
x_70 = l_Lean_Syntax_getArg(x_1, x_69);
lean_inc(x_2);
x_71 = l_Lake_getBinderIds(x_70, x_2, x_3);
lean_dec(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; size_t x_80; size_t x_81; lean_object* x_82; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unsigned_to_nat(2u);
x_75 = l_Lean_Syntax_getArg(x_1, x_74);
x_76 = lean_unsigned_to_nat(3u);
x_77 = l_Lean_Syntax_getArg(x_1, x_76);
lean_dec(x_1);
x_78 = l_Lake_expandBinderModifier(x_77);
lean_dec(x_77);
x_79 = lean_array_get_size(x_72);
x_80 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_81 = 0;
x_82 = l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__3(x_75, x_78, x_80, x_81, x_72, x_2, x_73);
lean_dec(x_75);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_71);
if (x_83 == 0)
{
return x_71;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_71, 0);
x_85 = lean_ctor_get(x_71, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_71);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
lean_dec(x_4);
lean_inc(x_1);
x_87 = l_Lake_expandBinderIdent(x_1, x_2, x_3);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = l_Lake_mkHoleFrom(x_1);
lean_dec(x_1);
x_91 = lean_box(0);
x_92 = 0;
x_93 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*3, x_92);
x_94 = l_Lake_mkHoleFrom___closed__7;
x_95 = lean_array_push(x_94, x_93);
lean_ctor_set(x_87, 0, x_95);
return x_87;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_87, 0);
x_97 = lean_ctor_get(x_87, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_87);
x_98 = l_Lake_mkHoleFrom(x_1);
lean_dec(x_1);
x_99 = lean_box(0);
x_100 = 0;
x_101 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*3, x_100);
x_102 = l_Lake_mkHoleFrom___closed__7;
x_103 = lean_array_push(x_102, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_97);
return x_104;
}
}
}
else
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_4);
lean_inc(x_1);
x_105 = l_Lake_expandBinderIdent(x_1, x_2, x_3);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = l_Lake_mkHoleFrom(x_1);
lean_dec(x_1);
x_109 = lean_box(0);
x_110 = 0;
x_111 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_108);
lean_ctor_set(x_111, 2, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*3, x_110);
x_112 = l_Lake_mkHoleFrom___closed__7;
x_113 = lean_array_push(x_112, x_111);
lean_ctor_set(x_105, 0, x_113);
return x_105;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_105, 0);
x_115 = lean_ctor_get(x_105, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_105);
x_116 = l_Lake_mkHoleFrom(x_1);
lean_dec(x_1);
x_117 = lean_box(0);
x_118 = 0;
x_119 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*3, x_118);
x_120 = l_Lake_mkHoleFrom___closed__7;
x_121 = lean_array_push(x_120, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_115);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_Lake_matchBinder___spec__3(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_BinderSyntaxView_mkBinder___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BinderSyntaxView_mkBinder___closed__5;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("}", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⦃", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⦄", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkBinder___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
switch (x_4) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = l_Lake_BinderSyntaxView_mkBinder___closed__1;
lean_inc(x_10);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lake_BinderSyntaxView_mkBinder___closed__3;
lean_inc(x_10);
x_14 = l_Lean_Syntax_node1(x_10, x_13, x_5);
x_15 = l_Lake_BinderSyntaxView_mkBinder___closed__4;
lean_inc(x_10);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_10);
x_17 = l_Lean_Syntax_node2(x_10, x_13, x_16, x_6);
x_18 = l_Lake_BinderSyntaxView_mkBinder___closed__6;
lean_inc(x_10);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lake_BinderSyntaxView_mkBinder___closed__7;
lean_inc(x_10);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lake_matchBinder___closed__2;
x_23 = l_Lean_Syntax_node5(x_10, x_22, x_12, x_14, x_17, x_21, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = l_Array_mkArray1___rarg(x_25);
x_27 = l_Lake_BinderSyntaxView_mkBinder___closed__5;
x_28 = l_Array_append___rarg(x_27, x_26);
lean_dec(x_26);
lean_inc(x_10);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_28);
x_30 = l_Lake_matchBinder___closed__2;
x_31 = l_Lean_Syntax_node5(x_10, x_30, x_12, x_14, x_17, x_29, x_19);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_2, 5);
x_36 = 0;
x_37 = l_Lean_SourceInfo_fromRef(x_35, x_36);
x_38 = l_Lake_BinderSyntaxView_mkBinder___closed__8;
lean_inc(x_37);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lake_BinderSyntaxView_mkBinder___closed__3;
lean_inc(x_37);
x_41 = l_Lean_Syntax_node1(x_37, x_40, x_33);
x_42 = l_Lake_BinderSyntaxView_mkBinder___closed__4;
lean_inc(x_37);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_37);
x_44 = l_Lean_Syntax_node2(x_37, x_40, x_43, x_34);
x_45 = l_Lake_BinderSyntaxView_mkBinder___closed__9;
lean_inc(x_37);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lake_matchBinder___closed__4;
x_48 = l_Lean_Syntax_node4(x_37, x_47, x_39, x_41, x_44, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
return x_49;
}
case 2:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_ctor_get(x_2, 5);
x_53 = 0;
x_54 = l_Lean_SourceInfo_fromRef(x_52, x_53);
x_55 = l_Lake_BinderSyntaxView_mkBinder___closed__10;
lean_inc(x_54);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lake_BinderSyntaxView_mkBinder___closed__3;
lean_inc(x_54);
x_58 = l_Lean_Syntax_node1(x_54, x_57, x_50);
x_59 = l_Lake_BinderSyntaxView_mkBinder___closed__4;
lean_inc(x_54);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_54);
x_61 = l_Lean_Syntax_node2(x_54, x_57, x_60, x_51);
x_62 = l_Lake_BinderSyntaxView_mkBinder___closed__11;
lean_inc(x_54);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_54);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lake_matchBinder___closed__6;
x_65 = l_Lean_Syntax_node4(x_54, x_64, x_56, x_58, x_61, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
return x_66;
}
default: 
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_ctor_get(x_2, 5);
x_70 = 0;
x_71 = l_Lean_SourceInfo_fromRef(x_69, x_70);
x_72 = l_Lake_BinderSyntaxView_mkBinder___closed__12;
lean_inc(x_71);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lake_BinderSyntaxView_mkBinder___closed__4;
lean_inc(x_71);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lake_BinderSyntaxView_mkBinder___closed__3;
lean_inc(x_71);
x_77 = l_Lean_Syntax_node2(x_71, x_76, x_67, x_75);
x_78 = l_Lake_BinderSyntaxView_mkBinder___closed__13;
lean_inc(x_71);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lake_matchBinder___closed__8;
x_81 = l_Lean_Syntax_node4(x_71, x_80, x_73, x_77, x_68, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_3);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BinderSyntaxView_mkBinder(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkArgument___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("namedArgument", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkArgument___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lake_mkHoleFrom___closed__1;
x_2 = l_Lake_mkHoleFrom___closed__2;
x_3 = l_Lake_mkHoleFrom___closed__3;
x_4 = l_Lake_BinderSyntaxView_mkArgument___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_BinderSyntaxView_mkArgument___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":=", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 5);
x_6 = 0;
x_7 = l_Lean_SourceInfo_fromRef(x_5, x_6);
x_8 = l_Lake_BinderSyntaxView_mkBinder___closed__1;
lean_inc(x_7);
x_9 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lake_BinderSyntaxView_mkArgument___closed__3;
lean_inc(x_7);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lake_BinderSyntaxView_mkBinder___closed__6;
lean_inc(x_7);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lake_BinderSyntaxView_mkArgument___closed__2;
lean_inc(x_4);
x_15 = l_Lean_Syntax_node5(x_7, x_14, x_9, x_4, x_11, x_4, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_BinderSyntaxView_mkArgument___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BinderSyntaxView_mkArgument(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_array_uget(x_1, x_3);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_9);
x_12 = l_Lake_BinderSyntaxView_mkBinder(x_9, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_push(x_11, x_13);
x_16 = l_Lake_BinderSyntaxView_mkArgument(x_9, x_5, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_array_push(x_10, x_18);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 0, x_20);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_4 = x_16;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_array_push(x_10, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
x_28 = 1;
x_29 = lean_usize_add(x_3, x_28);
x_3 = x_29;
x_4 = x_27;
x_6 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_1, x_3);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_13 = l_Lake_matchBinder(x_9, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__1(x_14, x_17, x_18, x_4, x_5, x_15);
lean_dec(x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
size_t x_23; size_t x_24; 
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
x_4 = x_20;
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_3, x_29);
x_3 = x_30;
x_4 = x_28;
x_6 = x_21;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
lean_inc(x_5);
x_38 = l_Lake_matchBinder(x_9, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_array_get_size(x_39);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = 0;
x_45 = l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__1(x_39, x_43, x_44, x_41, x_5, x_40);
lean_dec(x_39);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_50 = x_46;
} else {
 lean_dec_ref(x_46);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
x_52 = 1;
x_53 = lean_usize_add(x_3, x_52);
x_3 = x_53;
x_4 = x_51;
x_6 = x_47;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_5);
x_55 = lean_ctor_get(x_38, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_57 = x_38;
} else {
 lean_dec_ref(x_38);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
static lean_object* _init_l_Lake_expandBinders___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BinderSyntaxView_mkBinder___closed__5;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Lake_expandBinders___closed__1;
x_8 = l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__2(x_1, x_5, x_6, x_7, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_ctor_set(x_10, 1, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forInUnsafe_loop___at_Lake_expandBinders___spec__2(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_expandBinders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_expandBinders(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Binder(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_mkHoleFrom___closed__1 = _init_l_Lake_mkHoleFrom___closed__1();
lean_mark_persistent(l_Lake_mkHoleFrom___closed__1);
l_Lake_mkHoleFrom___closed__2 = _init_l_Lake_mkHoleFrom___closed__2();
lean_mark_persistent(l_Lake_mkHoleFrom___closed__2);
l_Lake_mkHoleFrom___closed__3 = _init_l_Lake_mkHoleFrom___closed__3();
lean_mark_persistent(l_Lake_mkHoleFrom___closed__3);
l_Lake_mkHoleFrom___closed__4 = _init_l_Lake_mkHoleFrom___closed__4();
lean_mark_persistent(l_Lake_mkHoleFrom___closed__4);
l_Lake_mkHoleFrom___closed__5 = _init_l_Lake_mkHoleFrom___closed__5();
lean_mark_persistent(l_Lake_mkHoleFrom___closed__5);
l_Lake_mkHoleFrom___closed__6 = _init_l_Lake_mkHoleFrom___closed__6();
lean_mark_persistent(l_Lake_mkHoleFrom___closed__6);
l_Lake_mkHoleFrom___closed__7 = _init_l_Lake_mkHoleFrom___closed__7();
lean_mark_persistent(l_Lake_mkHoleFrom___closed__7);
l_Lake_binder_formatter___closed__1 = _init_l_Lake_binder_formatter___closed__1();
lean_mark_persistent(l_Lake_binder_formatter___closed__1);
l_Lake_binder_formatter___closed__2 = _init_l_Lake_binder_formatter___closed__2();
lean_mark_persistent(l_Lake_binder_formatter___closed__2);
l_Lake_binder_parenthesizer___closed__1 = _init_l_Lake_binder_parenthesizer___closed__1();
lean_mark_persistent(l_Lake_binder_parenthesizer___closed__1);
l_Lake_binder_parenthesizer___closed__2 = _init_l_Lake_binder_parenthesizer___closed__2();
lean_mark_persistent(l_Lake_binder_parenthesizer___closed__2);
l_Lake_binder___closed__1 = _init_l_Lake_binder___closed__1();
lean_mark_persistent(l_Lake_binder___closed__1);
l_Lake_binder___closed__2 = _init_l_Lake_binder___closed__2();
lean_mark_persistent(l_Lake_binder___closed__2);
l_Lake_binder = _init_l_Lake_binder();
lean_mark_persistent(l_Lake_binder);
l_Lake_BinderSyntaxView_modifier_x3f___default = _init_l_Lake_BinderSyntaxView_modifier_x3f___default();
lean_mark_persistent(l_Lake_BinderSyntaxView_modifier_x3f___default);
l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__2);
l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_getBinderIds___spec__1___closed__3);
l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__1 = _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__1);
l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__2 = _init_l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshBinderName___at_Lake_expandBinderIdent___spec__2___closed__2);
l_Lake_matchBinder___closed__1 = _init_l_Lake_matchBinder___closed__1();
lean_mark_persistent(l_Lake_matchBinder___closed__1);
l_Lake_matchBinder___closed__2 = _init_l_Lake_matchBinder___closed__2();
lean_mark_persistent(l_Lake_matchBinder___closed__2);
l_Lake_matchBinder___closed__3 = _init_l_Lake_matchBinder___closed__3();
lean_mark_persistent(l_Lake_matchBinder___closed__3);
l_Lake_matchBinder___closed__4 = _init_l_Lake_matchBinder___closed__4();
lean_mark_persistent(l_Lake_matchBinder___closed__4);
l_Lake_matchBinder___closed__5 = _init_l_Lake_matchBinder___closed__5();
lean_mark_persistent(l_Lake_matchBinder___closed__5);
l_Lake_matchBinder___closed__6 = _init_l_Lake_matchBinder___closed__6();
lean_mark_persistent(l_Lake_matchBinder___closed__6);
l_Lake_matchBinder___closed__7 = _init_l_Lake_matchBinder___closed__7();
lean_mark_persistent(l_Lake_matchBinder___closed__7);
l_Lake_matchBinder___closed__8 = _init_l_Lake_matchBinder___closed__8();
lean_mark_persistent(l_Lake_matchBinder___closed__8);
l_Lake_BinderSyntaxView_mkBinder___closed__1 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__1();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__1);
l_Lake_BinderSyntaxView_mkBinder___closed__2 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__2();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__2);
l_Lake_BinderSyntaxView_mkBinder___closed__3 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__3();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__3);
l_Lake_BinderSyntaxView_mkBinder___closed__4 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__4();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__4);
l_Lake_BinderSyntaxView_mkBinder___closed__5 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__5();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__5);
l_Lake_BinderSyntaxView_mkBinder___closed__6 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__6();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__6);
l_Lake_BinderSyntaxView_mkBinder___closed__7 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__7();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__7);
l_Lake_BinderSyntaxView_mkBinder___closed__8 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__8();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__8);
l_Lake_BinderSyntaxView_mkBinder___closed__9 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__9();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__9);
l_Lake_BinderSyntaxView_mkBinder___closed__10 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__10();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__10);
l_Lake_BinderSyntaxView_mkBinder___closed__11 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__11();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__11);
l_Lake_BinderSyntaxView_mkBinder___closed__12 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__12();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__12);
l_Lake_BinderSyntaxView_mkBinder___closed__13 = _init_l_Lake_BinderSyntaxView_mkBinder___closed__13();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkBinder___closed__13);
l_Lake_BinderSyntaxView_mkArgument___closed__1 = _init_l_Lake_BinderSyntaxView_mkArgument___closed__1();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkArgument___closed__1);
l_Lake_BinderSyntaxView_mkArgument___closed__2 = _init_l_Lake_BinderSyntaxView_mkArgument___closed__2();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkArgument___closed__2);
l_Lake_BinderSyntaxView_mkArgument___closed__3 = _init_l_Lake_BinderSyntaxView_mkArgument___closed__3();
lean_mark_persistent(l_Lake_BinderSyntaxView_mkArgument___closed__3);
l_Lake_expandBinders___closed__1 = _init_l_Lake_expandBinders___closed__1();
lean_mark_persistent(l_Lake_expandBinders___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
