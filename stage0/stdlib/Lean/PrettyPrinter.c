// Lean compiler output
// Module: Lean.PrettyPrinter
// Imports: Init Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Parenthesizer Lean.PrettyPrinter.Formatter Lean.Parser.Module Lean.ParserCompiler
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__9;
static lean_object* l_Lean_PrettyPrinter_ppConst___closed__1;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__13;
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__1;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__7;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__4;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__6;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__5;
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227_(lean_object*);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__5;
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__7;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__8;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__1;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__14;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__2;
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppSignature___closed__1;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__3;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__5;
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__11;
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___rarg(lean_object*, lean_object*);
lean_object* l_Lean_instBEqLocalInstance___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__11;
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__16;
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppTactic___closed__2;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__1;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__4;
lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__3;
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__5;
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* lean_pp_expr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1___closed__1;
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__12;
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(lean_object*);
lean_object* l_instHashableArray___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__16;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ppFnsRef;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__10;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__14;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__15;
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__13;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__10;
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
static lean_object* l_Lean_PrettyPrinter_ppTerm___closed__2;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__3;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__8;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__6;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__7;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableLocalInstance___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__6;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__4;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__2;
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__9;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__12;
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__2;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__9;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM(lean_object*);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__9;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__5;
static lean_object* l_Lean_PrettyPrinter_ppModule___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppTerm___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppModule___closed__1;
lean_object* l_Lean_sanitizeSyntax(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
lean_object* l_Lean_PrettyPrinter_delabCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__2;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__4;
extern lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__17;
static lean_object* l_Lean_PrettyPrinter_ppTactic___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM(lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__12;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__18;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__10;
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__11;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__15;
lean_object* l_Lean_PrettyPrinter_parenthesizeCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppConst___lambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__13;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__3;
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___rarg___closed__2;
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__14;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__6;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__7;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__3___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__8;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Array_instBEqArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_module_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___rarg___closed__10;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppCommand___closed__1;
static lean_object* l_Lean_PrettyPrinter_ppCommand___closed__2;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__3;
static lean_object* l_Lean_PrettyPrinter_ppExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379_(lean_object*);
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__2;
x_2 = l_Lean_PPContext_runCoreM___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_pp_uniq", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PPContext_runCoreM___rarg___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__6;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__10() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_PPContext_runCoreM___rarg___closed__9;
x_3 = l_Lean_PPContext_runCoreM___rarg___closed__8;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__13;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__16() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_PPContext_runCoreM___rarg___closed__15;
x_3 = l_Lean_PPContext_runCoreM___rarg___closed__10;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<PrettyPrinter>", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___rarg___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("internal exception #", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_1, 5);
x_8 = l_Lean_Core_getMaxHeartbeats(x_5);
x_9 = l_Lean_PPContext_runCoreM___rarg___closed__4;
x_10 = l_Lean_PPContext_runCoreM___rarg___closed__7;
x_11 = l_Lean_PPContext_runCoreM___rarg___closed__10;
x_12 = l_Lean_PPContext_runCoreM___rarg___closed__14;
x_13 = l_Lean_PPContext_runCoreM___rarg___closed__16;
lean_inc(x_4);
x_14 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_11);
lean_ctor_set(x_14, 6, x_13);
x_15 = lean_io_get_num_heartbeats(x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_PPContext_runCoreM___rarg___closed__17;
x_19 = l_Lean_PPContext_runCoreM___rarg___closed__3;
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_unsigned_to_nat(1000u);
x_22 = lean_box(0);
x_23 = l_Lean_firstFrontendMacroScope;
x_24 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_5);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_ctor_set(x_25, 6, x_6);
lean_ctor_set(x_25, 7, x_7);
lean_ctor_set(x_25, 8, x_16);
lean_ctor_set(x_25, 9, x_8);
lean_ctor_set(x_25, 10, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*11, x_24);
x_26 = lean_st_mk_ref(x_14, x_17);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_27);
x_29 = lean_apply_3(x_2, x_25, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_27, x_31);
lean_dec(x_27);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_27);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_MessageData_toString(x_39, x_38);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_29);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_29, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_37, 0);
lean_inc(x_54);
lean_dec(x_37);
x_55 = l_Nat_repr(x_54);
x_56 = l_Lean_PPContext_runCoreM___rarg___closed__18;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_29, 0, x_58);
return x_29;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_29, 1);
lean_inc(x_59);
lean_dec(x_29);
x_60 = lean_ctor_get(x_37, 0);
lean_inc(x_60);
lean_dec(x_37);
x_61 = l_Nat_repr(x_60);
x_62 = l_Lean_PPContext_runCoreM___rarg___closed__18;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_64 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PPContext_runCoreM___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runCoreM___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_2);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_2);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqLocalInstance___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runMetaM___rarg___closed__5;
x_2 = lean_alloc_closure((void*)(l_Array_instBEqArray___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runMetaM___rarg___closed__6;
x_2 = l_Lean_Expr_instBEqExpr;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashableLocalInstance___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runMetaM___rarg___closed__8;
x_2 = lean_alloc_closure((void*)(l_instHashableArray___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runMetaM___rarg___closed__9;
x_2 = l_Lean_Expr_instHashableExpr;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___rarg___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runMetaM___rarg___closed__14;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___rarg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PPContext_runMetaM___rarg___closed__2;
x_2 = l_Lean_PPContext_runMetaM___rarg___closed__4;
x_3 = l_Lean_PPContext_runMetaM___rarg___closed__11;
x_4 = l_Lean_PPContext_runMetaM___rarg___closed__15;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_box(0);
x_6 = l_Lean_PPContext_runMetaM___rarg___closed__1;
x_7 = l_Lean_PPContext_runCoreM___rarg___closed__1;
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_8);
lean_ctor_set(x_9, 5, x_5);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_box(0);
x_12 = l_Lean_PPContext_runMetaM___rarg___closed__16;
x_13 = l_Lean_PPContext_runCoreM___rarg___closed__10;
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_MetaM_run_x27___rarg), 6, 3);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_9);
lean_closure_set(x_15, 2, x_14);
x_16 = l_Lean_PPContext_runCoreM___rarg(x_1, x_15, x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PPContext_runMetaM___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runMetaM___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_Lean_sanitizeSyntax(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_PrettyPrinter_parenthesizeCategory(x_1, x_10, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_PrettyPrinter_formatCategory(x_1, x_12, x_3, x_4, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_ppTerm___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_ppTerm___closed__2;
x_6 = l_Lean_PrettyPrinter_ppCategory(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PrettyPrinter_ppTerm(x_9, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Lean_LocalContext_sanitizeNames(x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppUsing___lambda__1), 7, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_1);
x_15 = l_Lean_PPContext_runCoreM___rarg___closed__1;
x_16 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg(x_13, x_15, x_14, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_PrettyPrinter_delab(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_ppExpr___closed__1;
x_8 = l_Lean_PrettyPrinter_ppUsing(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
x_9 = l_Lean_PrettyPrinter_delabCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_PrettyPrinter_ppTerm(x_12, x_6, x_7, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 2);
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
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___lambda__1), 8, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
x_16 = l_Lean_PPContext_runCoreM___rarg___closed__1;
x_17 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg(x_14, x_16, x_15, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppConst___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConst), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Lean_PrettyPrinter_ppConst___lambda__1___closed__1;
x_9 = l_Lean_PrettyPrinter_delabCore(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
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
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
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
static lean_object* _init_l_Lean_PrettyPrinter_ppConst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppConst___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_ppConst___closed__1;
x_8 = l_Lean_PrettyPrinter_ppUsing(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_uniq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_ppExprLegacy___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_ppExprLegacy___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_pp_expr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_7 = lean_box(0);
x_8 = l_Lean_PPContext_runMetaM___rarg___closed__1;
x_9 = l_Lean_PPContext_runCoreM___rarg___closed__1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_10);
lean_ctor_set(x_11, 5, x_7);
x_12 = lean_box(0);
x_13 = l_Lean_PPContext_runMetaM___rarg___closed__16;
x_14 = l_Lean_PPContext_runCoreM___rarg___closed__10;
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Core_getMaxHeartbeats(x_4);
x_18 = l_Lean_PPContext_runCoreM___rarg___closed__4;
x_19 = l_Lean_PrettyPrinter_ppExprLegacy___closed__3;
x_20 = l_Lean_PPContext_runCoreM___rarg___closed__14;
x_21 = l_Lean_PPContext_runCoreM___rarg___closed__16;
x_22 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_14);
lean_ctor_set(x_22, 6, x_21);
x_23 = lean_io_get_num_heartbeats(x_6);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PPContext_runCoreM___rarg___closed__17;
x_27 = l_Lean_PPContext_runCoreM___rarg___closed__3;
x_28 = lean_unsigned_to_nat(1000u);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = l_Lean_firstFrontendMacroScope;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 3, x_10);
lean_ctor_set(x_33, 4, x_28);
lean_ctor_set(x_33, 5, x_29);
lean_ctor_set(x_33, 6, x_30);
lean_ctor_set(x_33, 7, x_16);
lean_ctor_set(x_33, 8, x_24);
lean_ctor_set(x_33, 9, x_17);
lean_ctor_set(x_33, 10, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*11, x_32);
x_34 = lean_st_mk_ref(x_22, x_25);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_mk_ref(x_15, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_PrettyPrinter_ppExpr___closed__1;
lean_inc(x_35);
lean_inc(x_38);
x_41 = l_Lean_PrettyPrinter_ppUsing(x_5, x_40, x_11, x_38, x_33, x_35, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_st_ref_get(x_38, x_43);
lean_dec(x_38);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_get(x_35, x_45);
lean_dec(x_35);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_42);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_38);
lean_dec(x_35);
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_dec(x_41);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_MessageData_toString(x_53, x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_41);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_41, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_51, 0);
lean_inc(x_68);
lean_dec(x_51);
x_69 = l_Nat_repr(x_68);
x_70 = l_Lean_PPContext_runCoreM___rarg___closed__18;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_41, 0, x_72);
return x_41;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
lean_dec(x_41);
x_74 = lean_ctor_get(x_51, 0);
lean_inc(x_74);
lean_dec(x_51);
x_75 = l_Nat_repr(x_74);
x_76 = l_Lean_PPContext_runCoreM___rarg___closed__18;
x_77 = lean_string_append(x_76, x_75);
lean_dec(x_75);
x_78 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_ppTactic___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_ppTactic___closed__2;
x_6 = l_Lean_PrettyPrinter_ppCategory(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppCommand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_ppCommand___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_ppCommand___closed__2;
x_6 = l_Lean_PrettyPrinter_ppCategory(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppModule___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_parenthesizer), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppModule___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_formatter), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_ppModule___closed__1;
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
x_9 = l_Lean_PrettyPrinter_ppModule___closed__2;
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
static lean_object* _init_l_Lean_PrettyPrinter_ppSignature___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_levelParams(x_8);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_10, x_11);
x_13 = l_Lean_Expr_const___override(x_1, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_PrettyPrinter_ppSignature___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_PrettyPrinter_delabCore(x_13, x_14, x_15, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_PrettyPrinter_ppTerm(x_19, x_4, x_5, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_20);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
return x_7;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_7);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_1 = x_2;
goto _start;
}
case 4:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_5);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
case 5:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_12);
lean_ctor_set(x_1, 1, x_13);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
case 6:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_19);
lean_ctor_set(x_1, 0, x_20);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_21);
x_23 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
case 7:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_25);
x_28 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_26);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_29);
x_32 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_30);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
case 8:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 1);
x_36 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_38);
x_40 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
case 9:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_42);
x_45 = lean_array_get_size(x_43);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext___spec__1(x_46, x_47, x_43);
lean_ctor_set(x_1, 2, x_48);
lean_ctor_set(x_1, 1, x_44);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 2);
x_52 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_1);
x_53 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_50);
x_54 = lean_array_get_size(x_51);
x_55 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_56 = 0;
x_57 = l_Array_mapMUnsafe_map___at___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext___spec__1(x_55, x_56, x_51);
x_58 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_52);
return x_58;
}
}
default: 
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_4);
lean_ctor_set(x_2, 1, x_6);
x_7 = lean_apply_2(x_5, lean_box(0), x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_apply_2(x_10, lean_box(0), x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_14, lean_box(0), x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_apply_3(x_3, lean_box(0), x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Exception_isRuntime(x_9);
if (x_10 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_12);
lean_ctor_set(x_9, 1, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
}
else
{
return x_7;
}
}
else
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_18 == 0)
{
return x_7;
}
else
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_9, 1);
x_21 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_20);
lean_ctor_set(x_9, 1, x_21);
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
}
else
{
return x_7;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = l_Lean_Exception_isRuntime(x_26);
if (x_28 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
 x_31 = lean_box(0);
}
x_32 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_40 = x_26;
} else {
 lean_dec_ref(x_26);
 x_40 = lean_box(0);
}
x_41 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_39);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_27);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_27);
return x_44;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Exception_isRuntime(x_7);
if (x_8 == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_10);
lean_ctor_set(x_7, 1, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
}
else
{
return x_5;
}
}
else
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*11);
lean_dec(x_2);
if (x_16 == 0)
{
return x_5;
}
else
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 1);
x_19 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_18);
lean_ctor_set(x_7, 1, x_19);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_5, 0, x_23);
return x_5;
}
}
else
{
return x_5;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = l_Lean_Exception_isRuntime(x_24);
if (x_26 == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_29 = x_24;
} else {
 lean_dec_ref(x_24);
 x_29 = lean_box(0);
}
x_30 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_28);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*11);
lean_dec(x_2);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_25);
return x_35;
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_38 = x_24;
} else {
 lean_dec_ref(x_24);
 x_38 = lean_box(0);
}
x_39 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_25);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
return x_42;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Exception_isRuntime(x_9);
if (x_10 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_12);
lean_ctor_set(x_9, 1, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
}
else
{
return x_7;
}
}
else
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_18 == 0)
{
return x_7;
}
else
{
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_9, 1);
x_21 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_20);
lean_ctor_set(x_9, 1, x_21);
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
}
else
{
return x_7;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = l_Lean_Exception_isRuntime(x_26);
if (x_28 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
 x_31 = lean_box(0);
}
x_32 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_40 = x_26;
} else {
 lean_dec_ref(x_26);
 x_40 = lean_box(0);
}
x_41 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_39);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_27);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_27);
return x_44;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(0);
x_5 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1___closed__1;
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos), 8, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____spec__1), 6, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_Lean_PPContext_runMetaM___rarg(x_1, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTerm), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____spec__2), 4, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Lean_PPContext_runCoreM___rarg(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____spec__3), 6, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Lean_PPContext_runMetaM___rarg(x_1, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__1;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__2;
x_3 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ppFnsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__5;
x_3 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__4;
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PrettyPrinter", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__4;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__5;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__7;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__9;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__10;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__11;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__13;
x_2 = lean_unsigned_to_nat(1379u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__2;
x_3 = 0;
x_4 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__14;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("parenthesizer", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_registerParserCompilers___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_registerParserCompilers___closed__2;
x_2 = l_Lean_PrettyPrinter_registerParserCompilers___closed__3;
x_3 = l_Lean_PrettyPrinter_registerParserCompilers___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("formatter", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_registerParserCompilers___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_formatterAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_registerParserCompilers___closed__7;
x_2 = l_Lean_PrettyPrinter_registerParserCompilers___closed__8;
x_3 = l_Lean_PrettyPrinter_registerParserCompilers___closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_registerParserCompilers___closed__5;
x_3 = l_Lean_ParserCompiler_registerParserCompiler___rarg(x_2, x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_PrettyPrinter_registerParserCompilers___closed__10;
x_6 = l_Lean_ParserCompiler_registerParserCompiler___rarg(x_5, x_4);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ParserCompiler(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Formatter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PPContext_runCoreM___rarg___closed__1 = _init_l_Lean_PPContext_runCoreM___rarg___closed__1();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__1);
l_Lean_PPContext_runCoreM___rarg___closed__2 = _init_l_Lean_PPContext_runCoreM___rarg___closed__2();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__2);
l_Lean_PPContext_runCoreM___rarg___closed__3 = _init_l_Lean_PPContext_runCoreM___rarg___closed__3();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__3);
l_Lean_PPContext_runCoreM___rarg___closed__4 = _init_l_Lean_PPContext_runCoreM___rarg___closed__4();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__4);
l_Lean_PPContext_runCoreM___rarg___closed__5 = _init_l_Lean_PPContext_runCoreM___rarg___closed__5();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__5);
l_Lean_PPContext_runCoreM___rarg___closed__6 = _init_l_Lean_PPContext_runCoreM___rarg___closed__6();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__6);
l_Lean_PPContext_runCoreM___rarg___closed__7 = _init_l_Lean_PPContext_runCoreM___rarg___closed__7();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__7);
l_Lean_PPContext_runCoreM___rarg___closed__8 = _init_l_Lean_PPContext_runCoreM___rarg___closed__8();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__8);
l_Lean_PPContext_runCoreM___rarg___closed__9 = _init_l_Lean_PPContext_runCoreM___rarg___closed__9();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__9);
l_Lean_PPContext_runCoreM___rarg___closed__10 = _init_l_Lean_PPContext_runCoreM___rarg___closed__10();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__10);
l_Lean_PPContext_runCoreM___rarg___closed__11 = _init_l_Lean_PPContext_runCoreM___rarg___closed__11();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__11);
l_Lean_PPContext_runCoreM___rarg___closed__12 = _init_l_Lean_PPContext_runCoreM___rarg___closed__12();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__12);
l_Lean_PPContext_runCoreM___rarg___closed__13 = _init_l_Lean_PPContext_runCoreM___rarg___closed__13();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__13);
l_Lean_PPContext_runCoreM___rarg___closed__14 = _init_l_Lean_PPContext_runCoreM___rarg___closed__14();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__14);
l_Lean_PPContext_runCoreM___rarg___closed__15 = _init_l_Lean_PPContext_runCoreM___rarg___closed__15();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__15);
l_Lean_PPContext_runCoreM___rarg___closed__16 = _init_l_Lean_PPContext_runCoreM___rarg___closed__16();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__16);
l_Lean_PPContext_runCoreM___rarg___closed__17 = _init_l_Lean_PPContext_runCoreM___rarg___closed__17();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__17);
l_Lean_PPContext_runCoreM___rarg___closed__18 = _init_l_Lean_PPContext_runCoreM___rarg___closed__18();
lean_mark_persistent(l_Lean_PPContext_runCoreM___rarg___closed__18);
l_Lean_PPContext_runMetaM___rarg___closed__1 = _init_l_Lean_PPContext_runMetaM___rarg___closed__1();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__1);
l_Lean_PPContext_runMetaM___rarg___closed__2 = _init_l_Lean_PPContext_runMetaM___rarg___closed__2();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__2);
l_Lean_PPContext_runMetaM___rarg___closed__3 = _init_l_Lean_PPContext_runMetaM___rarg___closed__3();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__3);
l_Lean_PPContext_runMetaM___rarg___closed__4 = _init_l_Lean_PPContext_runMetaM___rarg___closed__4();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__4);
l_Lean_PPContext_runMetaM___rarg___closed__5 = _init_l_Lean_PPContext_runMetaM___rarg___closed__5();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__5);
l_Lean_PPContext_runMetaM___rarg___closed__6 = _init_l_Lean_PPContext_runMetaM___rarg___closed__6();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__6);
l_Lean_PPContext_runMetaM___rarg___closed__7 = _init_l_Lean_PPContext_runMetaM___rarg___closed__7();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__7);
l_Lean_PPContext_runMetaM___rarg___closed__8 = _init_l_Lean_PPContext_runMetaM___rarg___closed__8();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__8);
l_Lean_PPContext_runMetaM___rarg___closed__9 = _init_l_Lean_PPContext_runMetaM___rarg___closed__9();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__9);
l_Lean_PPContext_runMetaM___rarg___closed__10 = _init_l_Lean_PPContext_runMetaM___rarg___closed__10();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__10);
l_Lean_PPContext_runMetaM___rarg___closed__11 = _init_l_Lean_PPContext_runMetaM___rarg___closed__11();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__11);
l_Lean_PPContext_runMetaM___rarg___closed__12 = _init_l_Lean_PPContext_runMetaM___rarg___closed__12();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__12);
l_Lean_PPContext_runMetaM___rarg___closed__13 = _init_l_Lean_PPContext_runMetaM___rarg___closed__13();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__13);
l_Lean_PPContext_runMetaM___rarg___closed__14 = _init_l_Lean_PPContext_runMetaM___rarg___closed__14();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__14);
l_Lean_PPContext_runMetaM___rarg___closed__15 = _init_l_Lean_PPContext_runMetaM___rarg___closed__15();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__15);
l_Lean_PPContext_runMetaM___rarg___closed__16 = _init_l_Lean_PPContext_runMetaM___rarg___closed__16();
lean_mark_persistent(l_Lean_PPContext_runMetaM___rarg___closed__16);
l_Lean_PrettyPrinter_ppTerm___closed__1 = _init_l_Lean_PrettyPrinter_ppTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppTerm___closed__1);
l_Lean_PrettyPrinter_ppTerm___closed__2 = _init_l_Lean_PrettyPrinter_ppTerm___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_ppTerm___closed__2);
l_Lean_PrettyPrinter_ppExpr___closed__1 = _init_l_Lean_PrettyPrinter_ppExpr___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExpr___closed__1);
l_Lean_PrettyPrinter_ppConst___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_ppConst___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppConst___lambda__1___closed__1);
l_Lean_PrettyPrinter_ppConst___closed__1 = _init_l_Lean_PrettyPrinter_ppConst___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppConst___closed__1);
l_Lean_PrettyPrinter_ppExprLegacy___closed__1 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__1);
l_Lean_PrettyPrinter_ppExprLegacy___closed__2 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__2);
l_Lean_PrettyPrinter_ppExprLegacy___closed__3 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__3);
l_Lean_PrettyPrinter_ppTactic___closed__1 = _init_l_Lean_PrettyPrinter_ppTactic___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppTactic___closed__1);
l_Lean_PrettyPrinter_ppTactic___closed__2 = _init_l_Lean_PrettyPrinter_ppTactic___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_ppTactic___closed__2);
l_Lean_PrettyPrinter_ppCommand___closed__1 = _init_l_Lean_PrettyPrinter_ppCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppCommand___closed__1);
l_Lean_PrettyPrinter_ppCommand___closed__2 = _init_l_Lean_PrettyPrinter_ppCommand___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_ppCommand___closed__2);
l_Lean_PrettyPrinter_ppModule___closed__1 = _init_l_Lean_PrettyPrinter_ppModule___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppModule___closed__1);
l_Lean_PrettyPrinter_ppModule___closed__2 = _init_l_Lean_PrettyPrinter_ppModule___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_ppModule___closed__2);
l_Lean_PrettyPrinter_ppSignature___closed__1 = _init_l_Lean_PrettyPrinter_ppSignature___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppSignature___closed__1);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____lambda__1___closed__1);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__1 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__1);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__2 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__2);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__3 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__3);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__4 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__4);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__5 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227____closed__5);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1227_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__1 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__1);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__2 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__2);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__3 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__3);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__4 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__4);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__5 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__5);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__6 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__6);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__7 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__7);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__8 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__8);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__9 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__9);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__10 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__10);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__11 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__11);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__12 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__12);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__13 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__13);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__14 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379____closed__14);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1379_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_PrettyPrinter_registerParserCompilers___closed__1 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__1);
l_Lean_PrettyPrinter_registerParserCompilers___closed__2 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__2);
l_Lean_PrettyPrinter_registerParserCompilers___closed__3 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__3);
l_Lean_PrettyPrinter_registerParserCompilers___closed__4 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__4);
l_Lean_PrettyPrinter_registerParserCompilers___closed__5 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__5);
l_Lean_PrettyPrinter_registerParserCompilers___closed__6 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__6);
l_Lean_PrettyPrinter_registerParserCompilers___closed__7 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__7);
l_Lean_PrettyPrinter_registerParserCompilers___closed__8 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__8);
l_Lean_PrettyPrinter_registerParserCompilers___closed__9 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__9);
l_Lean_PrettyPrinter_registerParserCompilers___closed__10 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__10);
if (builtin) {res = l_Lean_PrettyPrinter_registerParserCompilers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
