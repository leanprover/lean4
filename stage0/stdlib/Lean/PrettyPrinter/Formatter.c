// Lean compiler output
// Module: Lean.PrettyPrinter.Formatter
// Imports: Lean.CoreM Lean.Parser.Extension Lean.Parser.StrInterpolation Lean.KeyedDeclsAttribute Lean.ParserCompiler.Attribute Lean.PrettyPrinter.Basic
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__4;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__7;
lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeForallFormatterAliasValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_take___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_instInhabitedFormat;
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f(lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__3;
LEAN_EXPORT uint8_t l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__1(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__2;
static lean_object* l_Lean_PrettyPrinter_formatCommand___closed__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1;
static lean_object* l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fill(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__1;
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__3;
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1;
static lean_object* l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_format___closed__1;
uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_instOrElseFormatterM(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__3;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__6;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_format___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___rarg(lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_FormatterM_orElse(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg(lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1;
static lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___rarg(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__4;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Format_isNil(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_format___lambda__4___closed__4;
extern lean_object* l_instInhabitedNat;
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_format___lambda__2(uint32_t);
static lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___closed__3;
static lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withoutInfo_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_FormatterM_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__12;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___at_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_recover_x27_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_pretty_printer_formatter_interpret_parser_descr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter___rarg(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_compileDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeForallForallFormatterAliasValue(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__3;
static lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__1;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__1;
static lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2;
static double l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__2(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__2;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__7;
static lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__6;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_formatTactic___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_format___lambda__4___closed__1;
lean_object* l_Lean_Parser_tokenFn(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___boxed(lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__1;
static lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__1;
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8;
static lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_formatTactic___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__8;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_formatTerm___closed__2;
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_antiquot_formatter(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_formatTerm___closed__1;
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304_(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__7;
static lean_object* l_Lean_PrettyPrinter_format___closed__2;
static lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__1;
uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_concat___closed__1;
static lean_object* l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__5;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__9;
LEAN_EXPORT lean_object* l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeFormatterAliasValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_pp_oneline;
static lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__11;
lean_object* l_Lean_Data_Trie_find_x3f_loop___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__5;
static lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
static lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__1;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__6;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ite(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
static lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__3;
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg(lean_object*);
lean_object* l_String_findAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__2;
lean_object* l_Lean_Parser_registerAliasCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp_macro_scopes(lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__4;
static lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_pretty_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_format___lambda__4___closed__6;
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__2___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1;
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_sepBy1NoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5205_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__6;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__2;
lean_object* l_Lean_getConstInfo___at_Lean_registerInitAttrUnsafe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__2;
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_format___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__2;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_format___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_getIndent(lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__6;
static lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
extern lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___at_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__10;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_format___lambda__4___closed__5;
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__1;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_recover_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_many1NoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__3;
static lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2;
static lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3;
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_format___lambda__4___closed__3;
static lean_object* l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__1;
static lean_object* l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
static lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__3;
static lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__5;
uint8_t l_Lean_Parser_isValidSyntaxNodeKind(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_whitespace(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1___closed__1;
static lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__5;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_formatCommand___closed__1;
static lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__6;
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__14;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___boxed(lean_object*);
static lean_object* _init_l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_backtrackExceptionId;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_FormatterM_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Exception_isInterrupt(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Exception_isRuntime(x_13);
if (x_16 == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1;
x_19 = lean_nat_dec_eq(x_18, x_17);
lean_dec(x_17);
if (x_19 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_11);
lean_dec(x_13);
x_20 = lean_st_ref_set(x_4, x_9, x_14);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_apply_6(x_2, x_22, x_3, x_4, x_5, x_6, x_21);
return x_23;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = l_Lean_Exception_isInterrupt(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_24);
if (x_27 == 0)
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1;
x_31 = lean_nat_dec_eq(x_30, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_24);
x_33 = lean_st_ref_set(x_4, x_9, x_25);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = lean_apply_6(x_2, x_35, x_3, x_4, x_5, x_6, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_25);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_25);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_FormatterM_orElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_FormatterM_orElse___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_FormatterM_orElse___rarg), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_instOrElseFormatterM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at_Lean_registerInitAttrUnsafe___spec__1(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_ConstantInfo_levelParams(x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_8, x_9);
x_11 = l_Lean_Expr_const___override(x_1, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = l_Lean_ConstantInfo_levelParams(x_12);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_14, x_15);
x_17 = l_Lean_Expr_const___override(x_1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 6);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 6);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_18, 1);
x_24 = l_Lean_PersistentArray_push___rarg(x_23, x_1);
lean_ctor_set(x_18, 1, x_24);
x_25 = lean_st_ref_set(x_3, x_17, x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = l_Lean_PersistentArray_push___rarg(x_34, x_1);
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_32);
lean_ctor_set(x_17, 6, x_36);
x_37 = lean_st_ref_set(x_3, x_17, x_19);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
x_44 = lean_ctor_get(x_17, 2);
x_45 = lean_ctor_get(x_17, 3);
x_46 = lean_ctor_get(x_17, 4);
x_47 = lean_ctor_get(x_17, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_48 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
x_49 = lean_ctor_get(x_18, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_51 = x_18;
} else {
 lean_dec_ref(x_18);
 x_51 = lean_box(0);
}
x_52 = l_Lean_PersistentArray_push___rarg(x_50, x_1);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 1);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_48);
x_54 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_43);
lean_ctor_set(x_54, 2, x_44);
lean_ctor_set(x_54, 3, x_45);
lean_ctor_set(x_54, 4, x_46);
lean_ctor_set(x_54, 5, x_47);
lean_ctor_set(x_54, 6, x_53);
x_55 = lean_st_ref_set(x_3, x_54, x_19);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__2;
x_3 = l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 6);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__3;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_pushInfoTree___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__4(x_17, x_2, x_3, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkConstWithLevelParams___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__2(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = l_Lean_LocalContext_empty;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_8);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3(x_15, x_4, x_5, x_9);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_5, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 6);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Environment_contains(x_10, x_1);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_11);
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = l_Lean_Elab_addConstInfo___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__1(x_2, x_1, x_18, x_4, x_5, x_14);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_ctor_get(x_28, 6);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Environment_contains(x_10, x_1);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_ctor_get_uint8(x_30, sizeof(void*)*2);
lean_dec(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
lean_inc(x_1);
x_36 = l_Lean_Elab_addConstInfo___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__1(x_2, x_1, x_35, x_4, x_5, x_29);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_1);
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_42 = x_36;
} else {
 lean_dec_ref(x_36);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid [formatter] argument, unknown syntax kind '", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_3);
x_11 = l_Lean_Attribute_Builtin_getIdent(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Syntax_getId(x_12);
if (x_1 == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_15 = x_30;
goto block_29;
}
else
{
lean_object* x_31; 
lean_inc(x_14);
lean_inc(x_10);
x_31 = lean_environment_find(x_10, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_15 = x_32;
goto block_29;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_10);
lean_dec(x_9);
x_33 = lean_box(0);
x_34 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__2(x_14, x_12, x_33, x_3, x_4, x_13);
lean_dec(x_3);
return x_34;
}
}
block_29:
{
uint8_t x_16; 
lean_dec(x_15);
x_16 = l_Lean_Parser_isValidSyntaxNodeKind(x_10, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_12);
x_17 = l_Lean_MessageData_ofName(x_14);
x_18 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__2;
if (lean_is_scalar(x_9)) {
 x_19 = lean_alloc_ctor(7, 2, 0);
} else {
 x_19 = x_9;
 lean_ctor_set_tag(x_19, 7);
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(x_21, x_3, x_4, x_13);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
x_27 = lean_box(0);
x_28 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__2(x_14, x_12, x_27, x_3, x_4, x_13);
lean_dec(x_3);
return x_28;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("builtin_formatter", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("formatter", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Formatter", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_3 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Register a formatter for a parser.\n\n  [formatter k] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `SyntaxNodeKind` `k`.", 144, 144);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__4___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4;
x_3 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9;
x_4 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8;
x_5 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10;
x_6 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("formatterAttribute", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_3 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12;
x_3 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__14;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkConstWithLevelParams___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoTree___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addConstInfo___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__4(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("combinator_formatter", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkCombinatorFormatterAttribute", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_3 = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Register a formatter for a parser combinator.\n\n  [combinator_formatter c] registers a declaration of type `Lean.PrettyPrinter.Formatter` for the `Parser` declaration `c`.\n  Note that, unlike with [formatter], this is not a node kind since combinators usually do not introduce their own node kinds.\n  The tagged declaration may optionally accept parameters corresponding to (a prefix of) those of `c`, where `Parser` is replaced\n  with `Formatter` in the parameter types.", 470, 470);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2;
x_3 = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__5;
x_4 = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__4;
x_5 = l_Lean_ParserCompiler_registerCombinatorAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_throwBacktrack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_throwBacktrack(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
x_12 = lean_st_ref_set(x_3, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 1);
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 2);
x_23 = lean_ctor_get(x_8, 2);
lean_inc(x_23);
lean_inc(x_19);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 1, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 2, x_22);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_apply_1(x_2, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_15);
x_16 = lean_st_ref_set(x_4, x_9, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_25 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 2);
x_26 = lean_ctor_get(x_9, 2);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_27 = lean_apply_1(x_2, x_21);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 1, x_24);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 2, x_25);
x_31 = lean_st_ref_set(x_4, x_30, x_10);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1;
x_2 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2;
x_3 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
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
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_getStack___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStack___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_getStack(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
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
x_11 = lean_array_get_size(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_getStackSize___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_getStackSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_getStackSize(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_dec(x_11);
lean_ctor_set(x_8, 2, x_1);
x_12 = lean_st_ref_set(x_3, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 1);
x_23 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_1);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 2, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_9);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setStack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_setStack(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 2);
x_12 = lean_array_push(x_11, x_1);
x_13 = 0;
lean_ctor_set(x_8, 2, x_12);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_13);
x_14 = lean_st_ref_set(x_3, x_8, x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_24 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 2);
x_25 = lean_ctor_get(x_8, 2);
lean_inc(x_25);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_26 = lean_array_push(x_25, x_1);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 2, x_24);
x_29 = lean_st_ref_set(x_3, x_28, x_9);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_15 = 0;
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_15);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 1, x_15);
x_16 = lean_st_ref_set(x_3, x_10, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get_uint8(x_10, sizeof(void*)*3 + 2);
x_25 = lean_ctor_get(x_10, 2);
lean_inc(x_25);
lean_inc(x_23);
lean_dec(x_10);
x_26 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_27 = 0;
x_28 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 2, x_24);
x_29 = lean_st_ref_set(x_3, x_28, x_11);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushWhitespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_pushWhitespace(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = l_Lean_PrettyPrinter_Formatter_pushWhitespace(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushLine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_pushLine(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_pushWhitespace(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushAlign___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_pushAlign(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_Syntax_Traverser_down(x_11, x_1);
lean_ctor_set(x_8, 0, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_23 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 1);
x_24 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 2);
x_25 = lean_ctor_get(x_8, 2);
lean_inc(x_25);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_26 = l_Lean_Syntax_Traverser_down(x_20, x_1);
x_27 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 1, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 2, x_24);
x_28 = lean_st_ref_set(x_3, x_27, x_9);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Syntax_Traverser_up(x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 2);
x_23 = lean_ctor_get(x_6, 2);
lean_inc(x_23);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_24 = l_Lean_Syntax_Traverser_up(x_18);
x_25 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 2, x_22);
x_26 = lean_st_ref_set(x_1, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Syntax_Traverser_left(x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 2);
x_23 = lean_ctor_get(x_6, 2);
lean_inc(x_23);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_24 = l_Lean_Syntax_Traverser_left(x_18);
x_25 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 1, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 2, x_22);
x_26 = lean_st_ref_set(x_1, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2(x_13, x_2, x_3, x_4, x_5, x_9);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___rarg(x_3, x_4, x_5, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goDown___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goUp___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_PrettyPrinter_Formatter_getStackSize___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_PrettyPrinter_Formatter_getStack___rarg(x_4, x_5, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
lean_inc(x_9);
x_17 = l_Array_extract___rarg(x_14, x_9, x_16);
lean_dec(x_16);
x_18 = lean_apply_1(x_1, x_17);
x_19 = l_Array_take___rarg(x_14, x_9);
lean_dec(x_9);
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_PrettyPrinter_Formatter_setStack(x_20, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_Format_isNil(x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
if (x_7 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_4);
x_2 = x_9;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
x_2 = x_9;
x_4 = x_6;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_concat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_concat___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
x_8 = l_Lean_PrettyPrinter_Formatter_fold(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_concat___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_concat___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_concat___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_indent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_inc(x_4);
lean_inc(x_3);
x_62 = l_Lean_PrettyPrinter_Formatter_fold(x_61, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_st_ref_take(x_4, x_63);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
lean_dec(x_3);
x_68 = l_Std_Format_getIndent(x_67);
lean_dec(x_67);
x_69 = lean_nat_to_int(x_68);
x_8 = x_69;
x_9 = x_65;
x_10 = x_66;
goto block_60;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_3);
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
lean_dec(x_2);
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_dec(x_64);
x_8 = x_70;
x_9 = x_71;
x_10 = x_72;
goto block_60;
}
}
else
{
uint8_t x_73; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_62);
if (x_73 == 0)
{
return x_62;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_62, 0);
x_75 = lean_ctor_get(x_62, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_62);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
block_60:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
x_16 = lean_nat_dec_lt(x_15, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_8);
x_17 = lean_st_ref_set(x_4, x_9, x_10);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_array_fget(x_12, x_15);
x_25 = lean_box(0);
x_26 = lean_array_fset(x_12, x_15, x_25);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_array_fset(x_26, x_15, x_27);
lean_dec(x_15);
lean_ctor_set(x_9, 2, x_28);
x_29 = lean_st_ref_set(x_4, x_9, x_10);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_25);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
x_36 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_37 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_38 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 2);
x_39 = lean_ctor_get(x_9, 2);
lean_inc(x_39);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_40 = lean_array_get_size(x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_40, x_41);
x_43 = lean_nat_dec_lt(x_42, x_40);
lean_dec(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_8);
x_44 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_35);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_36);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 1, x_37);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 2, x_38);
x_45 = lean_st_ref_set(x_4, x_44, x_10);
lean_dec(x_4);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_array_fget(x_39, x_42);
x_51 = lean_box(0);
x_52 = lean_array_fset(x_39, x_42, x_51);
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_50);
x_54 = lean_array_fset(x_52, x_42, x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_55, 0, x_34);
lean_ctor_set(x_55, 1, x_35);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_36);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 1, x_37);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 2, x_38);
x_56 = lean_st_ref_set(x_4, x_55, x_10);
lean_dec(x_4);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_51);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fill(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_inc(x_3);
x_8 = l_Lean_PrettyPrinter_Formatter_fold(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 2);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
x_18 = lean_nat_dec_lt(x_17, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_17);
x_19 = 0;
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_19);
x_20 = lean_st_ref_set(x_3, x_11, x_12);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_array_fget(x_14, x_17);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_14, x_17, x_28);
x_30 = 1;
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_fset(x_29, x_17, x_31);
lean_dec(x_17);
x_33 = 0;
lean_ctor_set(x_11, 2, x_32);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_33);
x_34 = lean_st_ref_set(x_3, x_11, x_12);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_28);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
x_41 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_42 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 2);
x_43 = lean_ctor_get(x_11, 2);
lean_inc(x_43);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_44 = lean_array_get_size(x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_44, x_45);
x_47 = lean_nat_dec_lt(x_46, x_44);
lean_dec(x_44);
if (x_47 == 0)
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_46);
x_48 = 0;
x_49 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 2, x_42);
x_50 = lean_st_ref_set(x_3, x_49, x_12);
lean_dec(x_3);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_array_fget(x_43, x_46);
x_56 = lean_box(0);
x_57 = lean_array_fset(x_43, x_46, x_56);
x_58 = 1;
x_59 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_array_fset(x_57, x_46, x_59);
lean_dec(x_46);
x_61 = 0;
x_62 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_62, 0, x_39);
lean_ctor_set(x_62, 1, x_40);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 2, x_42);
x_63 = lean_st_ref_set(x_3, x_62, x_12);
lean_dec(x_3);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_8);
if (x_67 == 0)
{
return x_8;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_8, 0);
x_69 = lean_ctor_get(x_8, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_8);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_group(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_inc(x_3);
x_8 = l_Lean_PrettyPrinter_Formatter_fold(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 2);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
x_18 = lean_nat_dec_lt(x_17, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_17);
x_19 = 0;
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_19);
x_20 = lean_st_ref_set(x_3, x_11, x_12);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_array_fget(x_14, x_17);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_14, x_17, x_28);
x_30 = 0;
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_fset(x_29, x_17, x_31);
lean_dec(x_17);
x_33 = 0;
lean_ctor_set(x_11, 2, x_32);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_33);
x_34 = lean_st_ref_set(x_3, x_11, x_12);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_28);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
x_41 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_42 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 2);
x_43 = lean_ctor_get(x_11, 2);
lean_inc(x_43);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_44 = lean_array_get_size(x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_44, x_45);
x_47 = lean_nat_dec_lt(x_46, x_44);
lean_dec(x_44);
if (x_47 == 0)
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_46);
x_48 = 0;
x_49 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 2, x_42);
x_50 = lean_st_ref_set(x_3, x_49, x_12);
lean_dec(x_3);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_array_fget(x_43, x_46);
x_56 = lean_box(0);
x_57 = lean_array_fset(x_43, x_46, x_56);
x_58 = 0;
x_59 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_array_fset(x_57, x_46, x_59);
lean_dec(x_46);
x_61 = 0;
x_62 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_62, 0, x_39);
lean_ctor_set(x_62, 1, x_40);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 2, x_42);
x_63 = lean_st_ref_set(x_3, x_62, x_12);
lean_dec(x_3);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_8);
if (x_67 == 0)
{
return x_8;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_8, 0);
x_69 = lean_ctor_get(x_8, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_8);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_inc(x_4);
x_11 = l_Lean_PrettyPrinter_Formatter_fold(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_19 = lean_st_ref_take(x_4, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_20, sizeof(void*)*3);
x_25 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 1);
x_26 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 2);
x_27 = lean_ctor_get(x_20, 2);
lean_inc(x_27);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_28 = x_20;
} else {
 lean_dec_ref(x_20);
 x_28 = lean_box(0);
}
x_43 = lean_array_get_size(x_27);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_43, x_44);
x_46 = lean_nat_dec_lt(x_45, x_43);
lean_dec(x_43);
if (x_46 == 0)
{
lean_dec(x_45);
x_29 = x_27;
goto block_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_array_fget(x_27, x_45);
x_48 = lean_box(0);
x_49 = lean_array_fset(x_27, x_45, x_48);
if (lean_obj_tag(x_47) == 7)
{
lean_object* x_54; 
x_54 = lean_array_fset(x_49, x_45, x_47);
lean_dec(x_45);
x_29 = x_54;
goto block_42;
}
else
{
x_50 = x_48;
goto block_53;
}
block_53:
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_50);
lean_inc(x_9);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_51, 1, x_47);
x_52 = lean_array_fset(x_49, x_45, x_51);
lean_dec(x_45);
x_29 = x_52;
goto block_42;
}
}
block_42:
{
lean_object* x_30; lean_object* x_31; 
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 3, 3);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_24);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 1, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 2, x_26);
x_31 = lean_st_ref_set(x_4, x_30, x_21);
lean_dec(x_4);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
x_13 = x_31;
goto block_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_13 = x_37;
goto block_18;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
x_13 = x_31;
goto block_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_13 = x_41;
goto block_18;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_19);
if (x_55 == 0)
{
x_13 = x_19;
goto block_18;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_19, 0);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_13 = x_58;
goto block_18;
}
}
block_18:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_11);
if (x_59 == 0)
{
return x_11;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_11, 0);
x_61 = lean_ctor_get(x_11, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_11);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withMaybeTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("choice", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getKind(x_9);
x_12 = l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__2;
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_st_ref_get(x_4, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_Exception_isInterrupt(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_19);
if (x_22 == 0)
{
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1;
x_25 = lean_nat_dec_eq(x_24, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_17);
lean_dec(x_19);
x_26 = lean_st_ref_set(x_4, x_15, x_20);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_27);
return x_28;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = l_Lean_Exception_isInterrupt(x_29);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_Exception_isRuntime(x_29);
if (x_32 == 0)
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_33; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1;
x_36 = lean_nat_dec_eq(x_35, x_34);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_38 = lean_st_ref_set(x_4, x_15, x_30);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_30);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_30);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_43, 0, x_1);
lean_closure_set(x_43, 1, x_2);
x_44 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_43, x_3, x_4, x_5, x_6, x_10);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_recover_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_recover_x27_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_mk_antiquot_formatter(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpretParserDescr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_pretty_printer_formatter_interpret_parser_descr(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_SourceInfo_getExprPos_x3f(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("missing", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_formatterAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_interpretParserDescr_x27___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<missing>", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__2;
x_8 = lean_name_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__3;
x_13 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__4;
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_PrettyPrinter_runForNodeKind___rarg(x_12, x_1, x_13, x_4, x_5, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_10);
lean_dec(x_10);
x_18 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_17, x_15, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_23 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__6;
x_24 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_23, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_3, x_4, x_5, x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_isAntiquotSuffixSplice(x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___rarg___lambda__1), 7, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
x_14 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_withAntiquotSuffixSplice_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_tokenWithAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_isTokenAntiquot(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_1, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1___closed__1;
x_8 = lean_st_ref_get(x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_4, 2);
x_12 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_10, x_11, x_1);
lean_dec(x_10);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_ctor_get(x_4, 2);
x_17 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_14, x_16, x_1);
lean_dec(x_14);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__2___rarg), 7, 0);
return x_3;
}
}
static double _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 3);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1;
x_23 = 0;
x_24 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_8);
x_28 = l_Lean_PersistentArray_push___rarg(x_21, x_12);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_st_ref_set(x_6, x_13, x_16);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint64_t x_36; lean_object* x_37; double x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1;
x_39 = 0;
x_40 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_39);
x_42 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2;
x_43 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_43);
lean_ctor_set(x_12, 0, x_8);
x_44 = l_Lean_PersistentArray_push___rarg(x_37, x_12);
x_45 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint64(x_45, sizeof(void*)*1, x_36);
lean_ctor_set(x_13, 3, x_45);
x_46 = lean_st_ref_set(x_6, x_13, x_16);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; double x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
x_53 = lean_ctor_get(x_13, 2);
x_54 = lean_ctor_get(x_13, 4);
x_55 = lean_ctor_get(x_13, 5);
x_56 = lean_ctor_get(x_13, 6);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_57 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_58 = lean_ctor_get(x_14, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_59 = x_14;
} else {
 lean_dec_ref(x_14);
 x_59 = lean_box(0);
}
x_60 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1;
x_61 = 0;
x_62 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_63 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set_float(x_63, sizeof(void*)*2, x_60);
lean_ctor_set_float(x_63, sizeof(void*)*2 + 8, x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*2 + 16, x_61);
x_64 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2;
x_65 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_10);
lean_ctor_set(x_65, 2, x_64);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_65);
lean_ctor_set(x_12, 0, x_8);
x_66 = l_Lean_PersistentArray_push___rarg(x_58, x_12);
if (lean_is_scalar(x_59)) {
 x_67 = lean_alloc_ctor(0, 1, 8);
} else {
 x_67 = x_59;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set_uint64(x_67, sizeof(void*)*1, x_57);
x_68 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_68, 0, x_51);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_53);
lean_ctor_set(x_68, 3, x_67);
lean_ctor_set(x_68, 4, x_54);
lean_ctor_set(x_68, 5, x_55);
lean_ctor_set(x_68, 6, x_56);
x_69 = lean_st_ref_set(x_6, x_68, x_16);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint64_t x_82; lean_object* x_83; lean_object* x_84; double x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_74 = lean_ctor_get(x_12, 1);
lean_inc(x_74);
lean_dec(x_12);
x_75 = lean_ctor_get(x_13, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_13, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_13, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_13, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_13, 5);
lean_inc(x_79);
x_80 = lean_ctor_get(x_13, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 x_81 = x_13;
} else {
 lean_dec_ref(x_13);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_83 = lean_ctor_get(x_14, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_84 = x_14;
} else {
 lean_dec_ref(x_14);
 x_84 = lean_box(0);
}
x_85 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1;
x_86 = 0;
x_87 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_88 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set_float(x_88, sizeof(void*)*2, x_85);
lean_ctor_set_float(x_88, sizeof(void*)*2 + 8, x_85);
lean_ctor_set_uint8(x_88, sizeof(void*)*2 + 16, x_86);
x_89 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2;
x_90 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_10);
lean_ctor_set(x_90, 2, x_89);
lean_inc(x_8);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_8);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_PersistentArray_push___rarg(x_83, x_91);
if (lean_is_scalar(x_84)) {
 x_93 = lean_alloc_ctor(0, 1, 8);
} else {
 x_93 = x_84;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set_uint64(x_93, sizeof(void*)*1, x_82);
if (lean_is_scalar(x_81)) {
 x_94 = lean_alloc_ctor(0, 7, 0);
} else {
 x_94 = x_81;
}
lean_ctor_set(x_94, 0, x_75);
lean_ctor_set(x_94, 1, x_76);
lean_ctor_set(x_94, 2, x_77);
lean_ctor_set(x_94, 3, x_93);
lean_ctor_set(x_94, 4, x_78);
lean_ctor_set(x_94, 5, x_79);
lean_ctor_set(x_94, 6, x_80);
x_95 = lean_st_ref_set(x_6, x_94, x_74);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 2);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_12 = 1;
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_12);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_23 = lean_ctor_get(x_8, 2);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 2, x_24);
x_26 = lean_st_ref_set(x_3, x_25, x_10);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_dec(x_7);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
uint8_t x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; 
x_33 = 0;
x_34 = 1;
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_33);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_34);
x_35 = lean_st_ref_set(x_3, x_8, x_31);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
x_44 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_45 = lean_ctor_get(x_8, 2);
lean_inc(x_45);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_46 = 0;
x_47 = 1;
x_48 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*3 + 1, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*3 + 2, x_47);
x_49 = lean_st_ref_set(x_3, x_48, x_31);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_3, x_4, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Syntax_getKind(x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rawStx", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__4), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__1;
lean_inc(x_1);
x_10 = l_Lean_Syntax_getKind(x_1);
x_11 = l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__2;
x_12 = lean_name_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__3;
x_14 = lean_name_eq(x_2, x_13);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_15 = 1;
x_16 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__4;
lean_inc(x_2);
x_17 = l_Lean_Name_toString(x_2, x_15, x_16);
x_18 = lean_box(x_15);
x_19 = lean_box(x_15);
x_20 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_18);
lean_closure_set(x_20, 3, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe), 6, 1);
lean_closure_set(x_21, 0, x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_20, x_21, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_apply_6(x_9, x_23, x_4, x_5, x_6, x_7, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
x_30 = 1;
x_31 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__4;
lean_inc(x_2);
x_32 = l_Lean_Name_toString(x_2, x_30, x_31);
x_33 = lean_box(x_30);
x_34 = lean_box(x_30);
x_35 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed), 9, 4);
lean_closure_set(x_35, 0, x_32);
lean_closure_set(x_35, 1, x_2);
lean_closure_set(x_35, 2, x_33);
lean_closure_set(x_35, 3, x_34);
x_36 = lean_box(0);
x_37 = 0;
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Syntax_formatStxAux(x_36, x_37, x_38, x_1);
x_40 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__3___boxed), 6, 1);
lean_closure_set(x_40, 0, x_39);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_41 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_35, x_40, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_apply_6(x_9, x_42, x_4, x_5, x_6, x_7, x_43);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_49 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__5;
x_50 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__6;
x_51 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__2___rarg), 7, 2);
lean_closure_set(x_51, 0, x_49);
lean_closure_set(x_51, 1, x_50);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_51, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_apply_6(x_9, x_53, x_4, x_5, x_6, x_7, x_54);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("format", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("formatting ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = 0;
x_12 = 1;
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_11);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 2, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__2;
x_20 = l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1(x_19, x_2, x_3, x_4, x_5, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_15);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5(x_17, x_1, x_24, x_2, x_3, x_4, x_5, x_23);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
x_31 = l_Lean_Syntax_formatStxAux(x_29, x_11, x_30, x_17);
x_32 = l_Lean_MessageData_ofFormat(x_31);
x_33 = l_Lean_indentD(x_32);
x_34 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__4;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_33);
lean_ctor_set(x_20, 0, x_34);
x_35 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_35);
lean_ctor_set(x_15, 0, x_20);
x_36 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_19, x_15, x_2, x_3, x_4, x_5, x_27);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5(x_17, x_1, x_37, x_2, x_3, x_4, x_5, x_38);
lean_dec(x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec(x_20);
x_41 = lean_box(0);
x_42 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
x_43 = l_Lean_Syntax_formatStxAux(x_41, x_11, x_42, x_17);
x_44 = l_Lean_MessageData_ofFormat(x_43);
x_45 = l_Lean_indentD(x_44);
x_46 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__4;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_48);
lean_ctor_set(x_15, 0, x_47);
x_49 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_19, x_15, x_2, x_3, x_4, x_5, x_40);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5(x_17, x_1, x_50, x_2, x_3, x_4, x_5, x_51);
lean_dec(x_50);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_15, 0);
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_15);
x_55 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__2;
x_56 = l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1(x_55, x_2, x_3, x_4, x_5, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_box(0);
x_61 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5(x_53, x_1, x_60, x_2, x_3, x_4, x_5, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_63 = x_56;
} else {
 lean_dec_ref(x_56);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
x_65 = lean_unsigned_to_nat(0u);
lean_inc(x_53);
x_66 = l_Lean_Syntax_formatStxAux(x_64, x_11, x_65, x_53);
x_67 = l_Lean_MessageData_ofFormat(x_66);
x_68 = l_Lean_indentD(x_67);
x_69 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__4;
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(7, 2, 0);
} else {
 x_70 = x_63;
 lean_ctor_set_tag(x_70, 7);
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_55, x_72, x_2, x_3, x_4, x_5, x_62);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5(x_53, x_1, x_74, x_2, x_3, x_4, x_5, x_75);
lean_dec(x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_77 = lean_ctor_get(x_8, 0);
x_78 = lean_ctor_get(x_8, 1);
x_79 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_80 = lean_ctor_get(x_8, 2);
lean_inc(x_80);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_8);
x_81 = 0;
x_82 = 1;
x_83 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_78);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set_uint8(x_83, sizeof(void*)*3, x_79);
lean_ctor_set_uint8(x_83, sizeof(void*)*3 + 1, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*3 + 2, x_82);
x_84 = lean_st_ref_set(x_3, x_83, x_9);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__2;
x_91 = l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1(x_90, x_2, x_3, x_4, x_5, x_88);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_89);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_box(0);
x_96 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5(x_87, x_1, x_95, x_2, x_3, x_4, x_5, x_94);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
x_99 = lean_box(0);
x_100 = lean_unsigned_to_nat(0u);
lean_inc(x_87);
x_101 = l_Lean_Syntax_formatStxAux(x_99, x_81, x_100, x_87);
x_102 = l_Lean_MessageData_ofFormat(x_101);
x_103 = l_Lean_indentD(x_102);
x_104 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__4;
if (lean_is_scalar(x_98)) {
 x_105 = lean_alloc_ctor(7, 2, 0);
} else {
 x_105 = x_98;
 lean_ctor_set_tag(x_105, 7);
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
if (lean_is_scalar(x_89)) {
 x_107 = lean_alloc_ctor(7, 2, 0);
} else {
 x_107 = x_89;
 lean_ctor_set_tag(x_107, 7);
}
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_90, x_107, x_2, x_3, x_4, x_5, x_97);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5(x_87, x_1, x_109, x_2, x_3, x_4, x_5, x_110);
lean_dec(x_109);
return x_111;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_PrettyPrinter_Formatter_fold(x_8, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*3 + 1);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Std_Format_getIndent(x_15);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_3, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_19, 2);
x_23 = lean_array_get_size(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
x_26 = lean_nat_dec_lt(x_25, x_23);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_25);
lean_free_object(x_17);
lean_dec(x_16);
x_27 = lean_st_ref_set(x_3, x_19, x_21);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_34 = lean_array_fget(x_22, x_25);
x_35 = lean_box(0);
x_36 = lean_array_fset(x_22, x_25, x_35);
x_37 = lean_nat_to_int(x_16);
lean_ctor_set_tag(x_17, 4);
lean_ctor_set(x_17, 1, x_34);
lean_ctor_set(x_17, 0, x_37);
x_38 = 1;
x_39 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_fset(x_36, x_25, x_39);
lean_dec(x_25);
lean_ctor_set(x_19, 2, x_40);
x_41 = lean_st_ref_set(x_3, x_19, x_21);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_35);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_46 = lean_ctor_get(x_17, 1);
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
x_49 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_50 = lean_ctor_get_uint8(x_19, sizeof(void*)*3 + 1);
x_51 = lean_ctor_get_uint8(x_19, sizeof(void*)*3 + 2);
x_52 = lean_ctor_get(x_19, 2);
lean_inc(x_52);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
x_53 = lean_array_get_size(x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_sub(x_53, x_54);
x_56 = lean_nat_dec_lt(x_55, x_53);
lean_dec(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_55);
lean_free_object(x_17);
lean_dec(x_16);
x_57 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_48);
lean_ctor_set(x_57, 2, x_52);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_49);
lean_ctor_set_uint8(x_57, sizeof(void*)*3 + 1, x_50);
lean_ctor_set_uint8(x_57, sizeof(void*)*3 + 2, x_51);
x_58 = lean_st_ref_set(x_3, x_57, x_46);
lean_dec(x_3);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_63 = lean_array_fget(x_52, x_55);
x_64 = lean_box(0);
x_65 = lean_array_fset(x_52, x_55, x_64);
x_66 = lean_nat_to_int(x_16);
lean_ctor_set_tag(x_17, 4);
lean_ctor_set(x_17, 1, x_63);
lean_ctor_set(x_17, 0, x_66);
x_67 = 1;
x_68 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_68, 0, x_17);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_69 = lean_array_fset(x_65, x_55, x_68);
lean_dec(x_55);
x_70 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_70, 0, x_47);
lean_ctor_set(x_70, 1, x_48);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_49);
lean_ctor_set_uint8(x_70, sizeof(void*)*3 + 1, x_50);
lean_ctor_set_uint8(x_70, sizeof(void*)*3 + 2, x_51);
x_71 = lean_st_ref_set(x_3, x_70, x_46);
lean_dec(x_3);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_75 = lean_ctor_get(x_17, 0);
x_76 = lean_ctor_get(x_17, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_17);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_75, sizeof(void*)*3);
x_80 = lean_ctor_get_uint8(x_75, sizeof(void*)*3 + 1);
x_81 = lean_ctor_get_uint8(x_75, sizeof(void*)*3 + 2);
x_82 = lean_ctor_get(x_75, 2);
lean_inc(x_82);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_83 = x_75;
} else {
 lean_dec_ref(x_75);
 x_83 = lean_box(0);
}
x_84 = lean_array_get_size(x_82);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_sub(x_84, x_85);
x_87 = lean_nat_dec_lt(x_86, x_84);
lean_dec(x_84);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_86);
lean_dec(x_16);
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 3, 3);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_77);
lean_ctor_set(x_88, 1, x_78);
lean_ctor_set(x_88, 2, x_82);
lean_ctor_set_uint8(x_88, sizeof(void*)*3, x_79);
lean_ctor_set_uint8(x_88, sizeof(void*)*3 + 1, x_80);
lean_ctor_set_uint8(x_88, sizeof(void*)*3 + 2, x_81);
x_89 = lean_st_ref_set(x_3, x_88, x_76);
lean_dec(x_3);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_94 = lean_array_fget(x_82, x_86);
x_95 = lean_box(0);
x_96 = lean_array_fset(x_82, x_86, x_95);
x_97 = lean_nat_to_int(x_16);
x_98 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
x_99 = 1;
x_100 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
x_101 = lean_array_fset(x_96, x_86, x_100);
lean_dec(x_86);
if (lean_is_scalar(x_83)) {
 x_102 = lean_alloc_ctor(0, 3, 3);
} else {
 x_102 = x_83;
}
lean_ctor_set(x_102, 0, x_77);
lean_ctor_set(x_102, 1, x_78);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_79);
lean_ctor_set_uint8(x_102, sizeof(void*)*3 + 1, x_80);
lean_ctor_set_uint8(x_102, sizeof(void*)*3 + 2, x_81);
x_103 = lean_st_ref_set(x_3, x_102, x_76);
lean_dec(x_3);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_3);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_11);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_11, 0);
lean_dec(x_108);
x_109 = lean_box(0);
lean_ctor_set(x_11, 0, x_109);
return x_11;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_11, 1);
lean_inc(x_110);
lean_dec(x_11);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_9);
if (x_113 == 0)
{
return x_9;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_9, 0);
x_115 = lean_ctor_get(x_9, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_9);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_categoryFormatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_indent), 7, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_fill(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = l_Lean_instInhabitedSyntax;
x_14 = l_Array_back_x21___rarg(x_13, x_12);
lean_dec(x_12);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l_instInhabitedNat;
x_17 = l_Array_back_x21___rarg(x_16, x_15);
lean_dec(x_15);
x_18 = lean_nat_sub(x_17, x_1);
lean_dec(x_17);
x_19 = l_Lean_Syntax_getArg(x_14, x_18);
lean_dec(x_18);
lean_dec(x_14);
x_20 = l_Lean_Syntax_getKind(x_19);
x_21 = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(x_20, x_3, x_4, x_5, x_6, x_10);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_parserOfStack_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_error_formatter___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_error_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_error_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_lookahead_formatter___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_lookahead_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___rarg), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtrack", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__1;
x_3 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkKind___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected node kind '", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', expected '", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Syntax_getKind(x_9);
x_12 = lean_name_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_free_object(x_7);
x_13 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_14 = l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1(x_13, x_2, x_3, x_4, x_5, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__3;
x_19 = lean_unbox(x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_14);
lean_dec(x_11);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_apply_6(x_18, x_20, x_2, x_3, x_4, x_5, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = l_Lean_MessageData_ofName(x_11);
x_23 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__5;
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_22);
lean_ctor_set(x_14, 0, x_23);
x_24 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__7;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_MessageData_ofName(x_1);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_13, x_29, x_2, x_3, x_4, x_5, x_17);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_6(x_18, x_31, x_2, x_3, x_4, x_5, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__3;
x_37 = lean_unbox(x_34);
lean_dec(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_apply_6(x_36, x_38, x_2, x_3, x_4, x_5, x_35);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = l_Lean_MessageData_ofName(x_11);
x_41 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__5;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__7;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_MessageData_ofName(x_1);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_13, x_48, x_2, x_3, x_4, x_5, x_35);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_apply_6(x_36, x_50, x_2, x_3, x_4, x_5, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_box(0);
lean_ctor_set(x_7, 0, x_53);
return x_7;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = l_Lean_Syntax_getKind(x_54);
x_57 = lean_name_eq(x_1, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_58 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_59 = l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1(x_58, x_2, x_3, x_4, x_5, x_55);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__3;
x_64 = lean_unbox(x_60);
lean_dec(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_56);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_apply_6(x_63, x_65, x_2, x_3, x_4, x_5, x_61);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = l_Lean_MessageData_ofName(x_56);
x_68 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__5;
if (lean_is_scalar(x_62)) {
 x_69 = lean_alloc_ctor(7, 2, 0);
} else {
 x_69 = x_62;
 lean_ctor_set_tag(x_69, 7);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__7;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_MessageData_ofName(x_1);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_58, x_75, x_2, x_3, x_4, x_5, x_61);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_apply_6(x_63, x_77, x_2, x_3, x_4, x_5, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_56);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_55);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkKind___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_checkKind___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_node_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_withFn_formatter___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withFn_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_withFn_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("foo", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2;
x_8 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__2___rarg), 7, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_13, x_5, x_6, x_7, x_8, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_tokenFn), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_parseToken___closed__2;
x_2 = l_Lean_PrettyPrinter_Formatter_parseToken___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_2 = l_Lean_FileMap_ofString(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_box(0);
x_13 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_14 = l_Lean_PrettyPrinter_Formatter_parseToken___closed__4;
lean_inc(x_1);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_box(0);
lean_inc(x_11);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_12);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
x_20 = l_Lean_PrettyPrinter_Formatter_parseToken___closed__3;
x_21 = l_Lean_Parser_ParserFn_run(x_20, x_15, x_17, x_18, x_19);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_4, 2);
x_26 = lean_box(0);
x_27 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_28 = l_Lean_PrettyPrinter_Formatter_parseToken___closed__4;
lean_inc(x_1);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_box(0);
lean_inc(x_25);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_26);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_dec(x_2);
x_33 = l_Lean_Parser_mkParserState(x_1);
lean_dec(x_1);
x_34 = l_Lean_PrettyPrinter_Formatter_parseToken___closed__3;
x_35 = l_Lean_Parser_ParserFn_run(x_34, x_29, x_31, x_32, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_23);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_parseToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_parseToken(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__1(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get(x_2, x_4);
x_8 = lean_uint32_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 1;
return x_11;
}
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__2(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
x_7 = lean_string_utf8_get(x_2, x_4);
x_8 = lean_uint32_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = 1;
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
lean_ctor_set(x_8, 1, x_12);
x_13 = lean_st_ref_set(x_3, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 1);
x_23 = lean_ctor_get_uint8(x_8, sizeof(void*)*3 + 2);
x_24 = lean_ctor_get(x_8, 2);
lean_inc(x_24);
lean_inc(x_20);
lean_dec(x_8);
x_25 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_26 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 1, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 2, x_23);
x_27 = lean_st_ref_set(x_3, x_26, x_9);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_9, x_11, x_10);
lean_inc(x_11);
x_13 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_9, x_12, x_11);
x_14 = lean_nat_sub(x_13, x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1;
x_18 = 10;
lean_inc(x_13);
x_19 = l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__1(x_18, x_9, x_11, x_13);
lean_dec(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_box(1);
x_21 = l_Lean_PrettyPrinter_Formatter_pushWhitespace(x_20, x_3, x_4, x_5, x_6, x_7);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_string_utf8_extract(x_9, x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_24, x_3, x_4, x_5, x_6, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_apply_6(x_17, x_26, x_3, x_4, x_5, x_6, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = lean_ctor_get(x_5, 2);
lean_inc(x_29);
x_30 = l_Std_Format_getIndent(x_29);
lean_dec(x_29);
x_31 = lean_nat_to_int(x_30);
x_32 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__2;
x_33 = lean_int_sub(x_32, x_31);
lean_dec(x_31);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_string_utf8_extract(x_9, x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
x_36 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__3;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push___boxed), 6, 1);
lean_closure_set(x_41, 0, x_40);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l_Lean_PrettyPrinter_Formatter_indent(x_41, x_34, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_apply_6(x_17, x_43, x_3, x_4, x_5, x_6, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_7);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
x_15 = lean_string_utf8_byte_size(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_15, x_16);
x_18 = lean_string_utf8_extract(x_1, x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
x_19 = lean_string_dec_eq(x_18, x_1);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_20 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
lean_ctor_set(x_11, 1, x_20);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_2);
x_21 = lean_st_ref_set(x_6, x_11, x_12);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = lean_apply_6(x_3, x_23, x_5, x_6, x_7, x_8, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_2);
x_25 = lean_st_ref_set(x_6, x_11, x_12);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = lean_apply_6(x_3, x_27, x_5, x_6, x_7, x_8, x_26);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 1);
x_31 = lean_ctor_get_uint8(x_11, sizeof(void*)*3 + 2);
x_32 = lean_ctor_get(x_11, 2);
lean_inc(x_32);
lean_inc(x_29);
lean_dec(x_11);
x_33 = lean_string_utf8_byte_size(x_1);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_33, x_34);
x_36 = lean_string_utf8_extract(x_1, x_35, x_33);
lean_dec(x_33);
lean_dec(x_35);
x_37 = lean_string_dec_eq(x_36, x_1);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_1);
x_38 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_39 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 1, x_30);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 2, x_31);
x_40 = lean_st_ref_set(x_6, x_39, x_12);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_apply_6(x_3, x_42, x_5, x_6, x_7, x_8, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_1);
lean_ctor_set(x_44, 2, x_32);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 1, x_30);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 2, x_31);
x_45 = lean_st_ref_set(x_6, x_44, x_12);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = lean_apply_6(x_3, x_47, x_5, x_6, x_7, x_8, x_46);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_5 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc(x_1);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_11, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_19);
x_21 = lean_string_utf8_extract(x_1, x_20, x_2);
lean_dec(x_20);
x_22 = lean_string_dec_eq(x_21, x_1);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
lean_dec(x_1);
x_23 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
lean_ctor_set(x_15, 1, x_23);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_3);
x_24 = lean_st_ref_set(x_7, x_15, x_16);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_apply_6(x_4, x_26, x_6, x_7, x_8, x_9, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_string_append(x_1, x_18);
lean_dec(x_18);
lean_ctor_set(x_15, 1, x_28);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_3);
x_29 = lean_st_ref_set(x_7, x_15, x_16);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = lean_apply_6(x_4, x_31, x_6, x_7, x_8, x_9, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
x_35 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 1);
x_36 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 2);
x_37 = lean_ctor_get(x_15, 2);
lean_inc(x_37);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_38);
x_40 = lean_string_utf8_extract(x_1, x_39, x_2);
lean_dec(x_39);
x_41 = lean_string_dec_eq(x_40, x_1);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_34);
lean_dec(x_1);
x_42 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_43 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_3);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 1, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 2, x_36);
x_44 = lean_st_ref_set(x_7, x_43, x_16);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_apply_6(x_4, x_46, x_6, x_7, x_8, x_9, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_string_append(x_1, x_34);
lean_dec(x_34);
x_49 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_37);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_3);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 1, x_35);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 2, x_36);
x_50 = lean_st_ref_set(x_7, x_49, x_16);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = lean_apply_6(x_4, x_52, x_6, x_7, x_8, x_9, x_51);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_box(1);
x_55 = l_Lean_PrettyPrinter_Formatter_pushWhitespace(x_54, x_6, x_7, x_8, x_9, x_10);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_1);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_1);
x_58 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_57, x_6, x_7, x_8, x_9, x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_st_ref_take(x_7, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_61, 1);
lean_dec(x_64);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_65);
x_67 = lean_string_utf8_extract(x_1, x_66, x_2);
lean_dec(x_66);
x_68 = lean_string_dec_eq(x_67, x_1);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_69 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
lean_ctor_set(x_61, 1, x_69);
lean_ctor_set_uint8(x_61, sizeof(void*)*3, x_3);
x_70 = lean_st_ref_set(x_7, x_61, x_62);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = lean_apply_6(x_4, x_72, x_6, x_7, x_8, x_9, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_ctor_set(x_61, 1, x_1);
lean_ctor_set_uint8(x_61, sizeof(void*)*3, x_3);
x_74 = lean_st_ref_set(x_7, x_61, x_62);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_box(0);
x_77 = lean_apply_6(x_4, x_76, x_6, x_7, x_8, x_9, x_75);
return x_77;
}
}
else
{
lean_object* x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_78 = lean_ctor_get(x_61, 0);
x_79 = lean_ctor_get_uint8(x_61, sizeof(void*)*3 + 1);
x_80 = lean_ctor_get_uint8(x_61, sizeof(void*)*3 + 2);
x_81 = lean_ctor_get(x_61, 2);
lean_inc(x_81);
lean_inc(x_78);
lean_dec(x_61);
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_82);
x_84 = lean_string_utf8_extract(x_1, x_83, x_2);
lean_dec(x_83);
x_85 = lean_string_dec_eq(x_84, x_1);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_1);
x_86 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_87 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_81);
lean_ctor_set_uint8(x_87, sizeof(void*)*3, x_3);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 1, x_79);
lean_ctor_set_uint8(x_87, sizeof(void*)*3 + 2, x_80);
x_88 = lean_st_ref_set(x_7, x_87, x_62);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_box(0);
x_91 = lean_apply_6(x_4, x_90, x_6, x_7, x_8, x_9, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_92, 0, x_78);
lean_ctor_set(x_92, 1, x_1);
lean_ctor_set(x_92, 2, x_81);
lean_ctor_set_uint8(x_92, sizeof(void*)*3, x_3);
lean_ctor_set_uint8(x_92, sizeof(void*)*3 + 1, x_79);
lean_ctor_set_uint8(x_92, sizeof(void*)*3 + 2, x_80);
x_93 = lean_st_ref_set(x_7, x_92, x_62);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_box(0);
x_96 = lean_apply_6(x_4, x_95, x_6, x_7, x_8, x_9, x_94);
return x_96;
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_53; uint8_t x_54; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___boxed), 7, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_53 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_54 = lean_string_dec_eq(x_14, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_string_utf8_byte_size(x_2);
x_56 = lean_unsigned_to_nat(0u);
lean_inc(x_55);
x_57 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_2, x_56, x_55);
x_58 = lean_string_utf8_extract(x_2, x_56, x_57);
lean_dec(x_57);
x_59 = lean_string_dec_eq(x_58, x_2);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_55);
lean_dec(x_11);
x_60 = lean_box(0);
x_15 = x_60;
goto block_52;
}
else
{
if (x_3 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_11);
x_61 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_2, x_55, x_56);
x_62 = lean_string_utf8_extract(x_2, x_61, x_55);
lean_dec(x_61);
lean_inc(x_62);
x_63 = lean_string_append(x_62, x_14);
lean_dec(x_14);
lean_inc(x_5);
x_64 = l_Lean_PrettyPrinter_Formatter_parseToken(x_63, x_5, x_6, x_7, x_8, x_12);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 2);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_string_utf8_byte_size(x_62);
lean_dec(x_62);
x_69 = lean_nat_dec_le(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
if (x_69 == 0)
{
uint8_t x_70; lean_object* x_71; 
x_70 = 1;
x_71 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_2, x_55, x_3, x_13, x_70, x_5, x_6, x_7, x_8, x_66);
lean_dec(x_55);
return x_71;
}
else
{
uint8_t x_72; lean_object* x_73; 
x_72 = 0;
x_73 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_2, x_55, x_3, x_13, x_72, x_5, x_6, x_7, x_8, x_66);
lean_dec(x_55);
return x_73;
}
}
else
{
uint8_t x_74; 
x_74 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
lean_dec(x_11);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_75 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_2, x_55, x_56);
x_76 = lean_string_utf8_extract(x_2, x_75, x_55);
lean_dec(x_75);
lean_inc(x_76);
x_77 = lean_string_append(x_76, x_14);
lean_dec(x_14);
lean_inc(x_5);
x_78 = l_Lean_PrettyPrinter_Formatter_parseToken(x_77, x_5, x_6, x_7, x_8, x_12);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 2);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_string_utf8_byte_size(x_76);
lean_dec(x_76);
x_83 = lean_nat_dec_le(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
uint8_t x_84; lean_object* x_85; 
x_84 = 1;
x_85 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_2, x_55, x_3, x_13, x_84, x_5, x_6, x_7, x_8, x_80);
lean_dec(x_55);
return x_85;
}
else
{
uint8_t x_86; lean_object* x_87; 
x_86 = 0;
x_87 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_2, x_55, x_3, x_13, x_86, x_5, x_6, x_7, x_8, x_80);
lean_dec(x_55);
return x_87;
}
}
else
{
uint8_t x_88; lean_object* x_89; 
lean_dec(x_14);
x_88 = 1;
x_89 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_2, x_55, x_3, x_13, x_88, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_55);
return x_89;
}
}
}
}
else
{
lean_object* x_90; 
lean_dec(x_11);
x_90 = lean_box(0);
x_15 = x_90;
goto block_52;
}
block_52:
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_15);
x_16 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_17 = lean_string_dec_eq(x_14, x_16);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_string_utf8_byte_size(x_2);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
lean_inc(x_2);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_18);
x_21 = lean_nat_sub(x_18, x_19);
x_22 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__2;
x_23 = l_Substring_prevn(x_20, x_22, x_21);
lean_dec(x_20);
x_24 = lean_nat_add(x_19, x_23);
lean_dec(x_23);
lean_inc(x_18);
lean_inc(x_2);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_18);
x_26 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__4;
x_27 = l_Substring_beq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_18);
lean_inc(x_2);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_28, x_5, x_6, x_7, x_8, x_12);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(x_2, x_3, x_13, x_30, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_box(1);
x_34 = l_Lean_PrettyPrinter_Formatter_pushWhitespace(x_33, x_5, x_6, x_7, x_8, x_12);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_2, x_19, x_18);
x_37 = lean_string_utf8_extract(x_2, x_19, x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_38, x_5, x_6, x_7, x_8, x_35);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(x_2, x_3, x_13, x_40, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_string_utf8_byte_size(x_2);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_2, x_44, x_43);
x_46 = lean_string_utf8_extract(x_2, x_44, x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_47, x_5, x_6, x_7, x_8, x_12);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(x_2, x_3, x_13, x_49, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_49);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_14 = 0;
lean_ctor_set(x_9, 1, x_13);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_14);
x_15 = lean_st_ref_set(x_4, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_apply_6(x_1, x_17, x_3, x_4, x_5, x_6, x_16);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 2);
x_22 = lean_ctor_get(x_9, 2);
lean_inc(x_22);
lean_inc(x_19);
lean_dec(x_9);
x_23 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 1, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 2, x_21);
x_26 = lean_st_ref_set(x_4, x_25, x_10);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_apply_6(x_1, x_28, x_3, x_4, x_5, x_6, x_27);
return x_29;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_pushToken___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_box(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___boxed), 9, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_12, x_14, x_13);
lean_inc(x_14);
x_16 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_12, x_15, x_14);
x_17 = lean_nat_sub(x_16, x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = 10;
lean_inc(x_16);
x_21 = l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__2(x_20, x_12, x_14, x_16);
lean_dec(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_string_utf8_extract(x_12, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
x_23 = l_Lean_PrettyPrinter_Formatter_pushToken___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_27, x_4, x_5, x_6, x_7, x_8);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__6(x_11, x_29, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_string_utf8_extract(x_12, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
x_33 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__3;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_37, x_4, x_5, x_6, x_7, x_8);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__6(x_11, x_39, x_4, x_5, x_6, x_7, x_40);
lean_dec(x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
x_42 = lean_box(0);
x_43 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5(x_1, x_2, x_3, x_42, x_4, x_5, x_6, x_7, x_8);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box(0);
x_45 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5(x_1, x_2, x_3, x_44, x_4, x_5, x_6, x_7, x_8);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_String_anyAux___at_Lean_PrettyPrinter_Formatter_pushToken___spec__2(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__3(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__4(x_1, x_2, x_11, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_pushToken___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_PrettyPrinter_Formatter_pushToken(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__3;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected syntax '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', expected symbol '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.PrettyPrinter.Formatter", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.PrettyPrinter.Formatter.symbolNoAntiquot.formatter", 55, 55);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__5;
x_2 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__6;
x_3 = lean_unsigned_to_nat(410u);
x_4 = lean_unsigned_to_nat(42u);
x_5 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__7;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Syntax_isToken(x_1, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_13 = l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1(x_12, x_2, x_3, x_4, x_5, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_13, 1);
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = 0;
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_formatStxAux(x_21, x_22, x_23, x_9);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__2;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set(x_13, 0, x_26);
x_27 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__4;
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_27);
lean_ctor_set(x_7, 0, x_13);
x_28 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_12, x_31, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_box(0);
x_37 = 0;
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Syntax_formatStxAux(x_36, x_37, x_38, x_9);
x_40 = l_Lean_MessageData_ofFormat(x_39);
x_41 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__4;
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_43);
lean_ctor_set(x_7, 0, x_42);
x_44 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_7);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_12, x_47, x_2, x_3, x_4, x_5, x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_49);
return x_50;
}
}
}
else
{
lean_free_object(x_7);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
x_52 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_9);
lean_dec(x_9);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(x_55, 0, x_51);
lean_closure_set(x_55, 1, x_1);
lean_closure_set(x_55, 2, x_54);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_56 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_52, x_55, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_3, x_4, x_5, x_57);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_9);
lean_dec(x_1);
x_63 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__8;
x_64 = l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1(x_63, x_2, x_3, x_4, x_5, x_10);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_7, 0);
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_7);
x_67 = l_Lean_Syntax_isToken(x_1, x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_69 = l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1(x_68, x_2, x_3, x_4, x_5, x_66);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_65);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
x_76 = lean_box(0);
x_77 = 0;
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Syntax_formatStxAux(x_76, x_77, x_78, x_65);
x_80 = l_Lean_MessageData_ofFormat(x_79);
x_81 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__2;
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(7, 2, 0);
} else {
 x_82 = x_75;
 lean_ctor_set_tag(x_82, 7);
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__4;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_stringToMessageData(x_1);
lean_dec(x_1);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3(x_68, x_88, x_2, x_3, x_4, x_5, x_74);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg(x_90);
return x_91;
}
}
else
{
if (lean_obj_tag(x_65) == 2)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_65, 0);
lean_inc(x_92);
x_93 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_65);
lean_dec(x_65);
x_94 = 0;
x_95 = lean_box(x_94);
x_96 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(x_96, 0, x_92);
lean_closure_set(x_96, 1, x_1);
lean_closure_set(x_96, 2, x_95);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_97 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_93, x_96, x_2, x_3, x_4, x_5, x_66);
lean_dec(x_93);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_3, x_4, x_5, x_98);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_102 = x_97;
} else {
 lean_dec_ref(x_97);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_65);
lean_dec(x_1);
x_104 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__8;
x_105 = l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1(x_104, x_2, x_3, x_4, x_5, x_66);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_nonReservedSymbolNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_8 = lean_string_push(x_7, x_1);
x_9 = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawCh_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_8 = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not an atom: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__3;
x_14 = lean_string_utf8_byte_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_14, x_15);
x_17 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_1, x_16, x_14);
x_18 = lean_string_utf8_extract(x_1, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_string_dec_eq(x_12, x_18);
lean_dec(x_18);
lean_dec(x_12);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_PrettyPrinter_Formatter_pushToken(x_11, x_2, x_20, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_apply_6(x_13, x_22, x_3, x_4, x_5, x_6, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_2);
x_29 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_PrettyPrinter_Formatter_pushToken(x_11, x_1, x_29, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_6(x_13, x_31, x_3, x_4, x_5, x_6, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_8, 1);
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_41 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_39);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_MessageData_ofSyntax(x_43);
x_46 = l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__2;
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_45);
lean_ctor_set(x_41, 0, x_46);
x_47 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_47);
lean_ctor_set(x_8, 0, x_41);
x_48 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_8, x_3, x_4, x_5, x_6, x_44);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = l_Lean_MessageData_ofSyntax(x_49);
x_52 = l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__2;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_54);
lean_ctor_set(x_8, 0, x_53);
x_55 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_8, x_3, x_4, x_5, x_6, x_50);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_8, 1);
lean_inc(x_56);
lean_dec(x_8);
x_57 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = l_Lean_MessageData_ofSyntax(x_58);
x_62 = l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__2;
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(7, 2, 0);
} else {
 x_63 = x_60;
 lean_ctor_set_tag(x_63, 7);
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_65, x_3, x_4, x_5, x_6, x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Data_Trie_find_x3f_loop___rarg(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not an ident: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_PrettyPrinter_Formatter_checkKind(x_6, x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 2:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_MessageData_ofSyntax(x_17);
x_20 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
x_21 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_21);
lean_ctor_set(x_10, 0, x_15);
x_22 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_10, x_1, x_2, x_3, x_4, x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = l_Lean_MessageData_ofSyntax(x_23);
x_26 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_28);
lean_ctor_set(x_10, 0, x_27);
x_29 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_10, x_1, x_2, x_3, x_4, x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_10);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_dec(x_9);
x_31 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = l_Lean_MessageData_ofSyntax(x_32);
x_36 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(7, 2, 0);
} else {
 x_37 = x_34;
 lean_ctor_set_tag(x_37, 7);
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_39, x_1, x_2, x_3, x_4, x_33);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_40;
}
}
case 3:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_dec(x_9);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_10, 2);
lean_inc(x_43);
x_44 = lean_simp_macro_scopes(x_43);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lambda__1___boxed), 2, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_getExprPos_x3f(x_10);
lean_dec(x_10);
x_48 = 1;
x_49 = l_Lean_Name_toString(x_44, x_48, x_46);
x_50 = lean_box(x_48);
x_51 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushToken___boxed), 8, 3);
lean_closure_set(x_51, 0, x_42);
lean_closure_set(x_51, 1, x_49);
lean_closure_set(x_51, 2, x_50);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_52 = l_Lean_PrettyPrinter_Formatter_withMaybeTag(x_47, x_51, x_1, x_2, x_3, x_4, x_41);
lean_dec(x_47);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_2, x_3, x_4, x_53);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
default: 
{
uint8_t x_59; 
lean_dec(x_10);
x_59 = !lean_is_exclusive(x_9);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_9, 1);
x_61 = lean_ctor_get(x_9, 0);
lean_dec(x_61);
x_62 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_60);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = l_Lean_MessageData_ofSyntax(x_64);
x_67 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
lean_ctor_set_tag(x_62, 7);
lean_ctor_set(x_62, 1, x_66);
lean_ctor_set(x_62, 0, x_67);
x_68 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_68);
lean_ctor_set(x_9, 0, x_62);
x_69 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_9, x_1, x_2, x_3, x_4, x_65);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_62, 0);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_62);
x_72 = l_Lean_MessageData_ofSyntax(x_70);
x_73 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_75);
lean_ctor_set(x_9, 0, x_74);
x_76 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_9, x_1, x_2, x_3, x_4, x_71);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_77 = lean_ctor_get(x_9, 1);
lean_inc(x_77);
lean_dec(x_9);
x_78 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = l_Lean_MessageData_ofSyntax(x_79);
x_83 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(7, 2, 0);
} else {
 x_84 = x_81;
 lean_ctor_set_tag(x_84, 7);
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_86, x_1, x_2, x_3, x_4, x_80);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_7);
if (x_88 == 0)
{
return x_7;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_7, 0);
x_90 = lean_ctor_get(x_7, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_7);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___lambda__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_PrettyPrinter_Formatter_checkKind(x_6, x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 2:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_MessageData_ofSyntax(x_17);
x_20 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
x_21 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_21);
lean_ctor_set(x_10, 0, x_15);
x_22 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_10, x_1, x_2, x_3, x_4, x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = l_Lean_MessageData_ofSyntax(x_23);
x_26 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_28);
lean_ctor_set(x_10, 0, x_27);
x_29 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_10, x_1, x_2, x_3, x_4, x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_10);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_dec(x_9);
x_31 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = l_Lean_MessageData_ofSyntax(x_32);
x_36 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(7, 2, 0);
} else {
 x_37 = x_34;
 lean_ctor_set_tag(x_37, 7);
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_39, x_1, x_2, x_3, x_4, x_33);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_40;
}
}
case 3:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_dec(x_9);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_10, 2);
lean_inc(x_43);
lean_dec(x_10);
x_44 = 1;
x_45 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__4;
x_46 = l_Lean_Name_toString(x_43, x_44, x_45);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_47 = l_Lean_PrettyPrinter_Formatter_pushToken(x_42, x_46, x_44, x_1, x_2, x_3, x_4, x_41);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_2, x_3, x_4, x_48);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
default: 
{
uint8_t x_54; 
lean_dec(x_10);
x_54 = !lean_is_exclusive(x_9);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_9, 1);
x_56 = lean_ctor_get(x_9, 0);
lean_dec(x_56);
x_57 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_55);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
x_61 = l_Lean_MessageData_ofSyntax(x_59);
x_62 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_61);
lean_ctor_set(x_57, 0, x_62);
x_63 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_63);
lean_ctor_set(x_9, 0, x_57);
x_64 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_9, x_1, x_2, x_3, x_4, x_60);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_57);
x_67 = l_Lean_MessageData_ofSyntax(x_65);
x_68 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_70);
lean_ctor_set(x_9, 0, x_69);
x_71 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_9, x_1, x_2, x_3, x_4, x_66);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
lean_dec(x_9);
x_73 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_2, x_3, x_4, x_72);
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
x_77 = l_Lean_MessageData_ofSyntax(x_74);
x_78 = l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4;
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(7, 2, 0);
} else {
 x_79 = x_76;
 lean_ctor_set_tag(x_79, 7);
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_81, x_1, x_2, x_3, x_4, x_75);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_7);
if (x_83 == 0)
{
return x_7;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_7, 0);
x_85 = lean_ctor_get(x_7, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_7);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_rawIdentNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_identEq_formatter___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_identEq_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_identEq_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = l_Lean_instInhabitedSyntax;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_17, x_16, x_18);
lean_dec(x_16);
switch (lean_obj_tag(x_19)) {
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
x_20 = l_Lean_MessageData_ofSyntax(x_1);
x_21 = l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_24, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
case 2:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_PrettyPrinter_Formatter_pushToken(x_26, x_27, x_28, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
default: 
{
lean_object* x_36; 
lean_dec(x_19);
x_36 = lean_box(0);
x_8 = x_36;
goto block_15;
}
}
}
case 2:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l_Lean_PrettyPrinter_Formatter_pushToken(x_37, x_38, x_39, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_4, x_5, x_6, x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
default: 
{
lean_object* x_47; 
x_47 = lean_box(0);
x_8 = x_47;
goto block_15;
}
}
block_15:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
x_9 = l_Lean_MessageData_ofSyntax(x_1);
x_10 = l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__2;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___spec__1(x_13, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_PrettyPrinter_Formatter_checkKind(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(x_8, x_13, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(x_8, x_20, x_2, x_3, x_4, x_5, x_9);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_visitAtom___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("char", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scientific", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fieldIdx", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__2;
x_7 = l_Lean_PrettyPrinter_Formatter_visitAtom(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_5(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_4 = x_14;
x_5 = lean_box(0);
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___spec__1___boxed), 10, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, lean_box(0));
x_13 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_forM_loop___at_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_many1NoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = l_Array_isEmpty___rarg(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_1, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_14, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getKind(x_8);
x_11 = l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__2;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_Formatter_manyNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___at_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_mod(x_15, x_16);
x_18 = lean_nat_dec_eq(x_17, x_12);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = lean_apply_5(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_5 = x_15;
x_6 = lean_box(0);
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_26 = lean_apply_5(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_5 = x_15;
x_6 = lean_box(0);
x_11 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_11);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getArgs(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Nat_forRevM_loop___at_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter___spec__1___boxed), 11, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_9);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_12);
lean_closure_set(x_13, 5, lean_box(0));
x_14 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_13, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___at_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_forRevM_loop___at_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_sepBy1NoAntiquot_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_withoutInfo_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_12 = lean_string_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_6);
x_13 = lean_box(1);
x_14 = l_Lean_PrettyPrinter_Formatter_pushWhitespace(x_13, x_1, x_2, x_3, x_4, x_9);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_box(0);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_20 = lean_string_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(1);
x_22 = l_Lean_PrettyPrinter_Formatter_pushWhitespace(x_21, x_1, x_2, x_3, x_4, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkPrec_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkLhsPrec_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_setLhsPrec_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkStackTop_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 1);
lean_dec(x_9);
x_10 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_11 = 0;
lean_ctor_set(x_6, 1, x_10);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_11);
x_12 = lean_st_ref_set(x_1, x_6, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 1);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*3 + 2);
x_22 = lean_ctor_get(x_6, 2);
lean_inc(x_22);
lean_inc(x_19);
lean_dec(x_6);
x_23 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 1, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*3 + 2, x_21);
x_26 = lean_st_ref_set(x_1, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_checkNoWsBefore_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkTailWs_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkColEq_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkColGe_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkColGt_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_eoi_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_eoi_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_eoi_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_checkNoImmediateColon_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_skip_formatter___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_skip_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_skip_formatter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_pushNone_formatter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_pushNone_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_pushNone_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Formatter_hygieneInfoNoAntiquot_formatter(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStrLitKind", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__2;
x_14 = l_Lean_Syntax_isLit_x3f(x_13, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_5(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
lean_ctor_set_tag(x_14, 3);
x_26 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_14, x_6, x_7, x_8, x_9, x_10);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_7, x_8, x_9, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_5 = x_29;
x_10 = x_30;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l___private_Lean_PrettyPrinter_Formatter_0__Lean_PrettyPrinter_Formatter_push(x_35, x_6, x_7, x_8, x_9, x_10);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Syntax_MonadTraverser_goLeft___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__4___rarg(x_7, x_8, x_9, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_3 = x_42;
x_5 = x_39;
x_10 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Formatter_optionalNoAntiquot_formatter___spec__1___rarg___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Syntax_MonadTraverser_getCur___at_Lean_PrettyPrinter_Formatter_visitArgs___spec__1___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_11 = l_Array_reverse___rarg(x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_15 = l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1;
x_16 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_15, x_2, x_3, x_4, x_5, x_9);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_18 = l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1;
x_19 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_18, x_2, x_3, x_4, x_5, x_9);
return x_19;
}
else
{
size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1;
x_23 = lean_box_usize(x_20);
x_24 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___boxed), 10, 5);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_11);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_21);
x_25 = l_Lean_PrettyPrinter_Formatter_visitArgs(x_24, x_2, x_3, x_4, x_5, x_9);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ite(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_ite___rarg___boxed), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_ite___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_PrettyPrinter_Formatter_ite___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5205_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Formatter_registerAlias___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_registerAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_Formatter_registerAlias___closed__1;
x_5 = l_Lean_Parser_registerAliasCore___rarg(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeFormatterAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeForallFormatterAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Formatter_instCoeForallForallFormatterAliasValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pp", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("oneline", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__1;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(pretty printer) elide all but first line of pretty printer output", 66, 66);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__1;
x_3 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_3 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__1;
x_4 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__3;
x_3 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__5;
x_4 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__6;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_format___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 3);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; double x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1;
x_21 = 0;
x_22 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_23 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_float(x_23, sizeof(void*)*2, x_20);
lean_ctor_set_float(x_23, sizeof(void*)*2 + 8, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 16, x_21);
x_24 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2;
x_25 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_8);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_25);
lean_ctor_set(x_10, 0, x_6);
x_26 = l_Lean_PersistentArray_push___rarg(x_19, x_10);
lean_ctor_set(x_12, 0, x_26);
x_27 = lean_st_ref_set(x_4, x_11, x_14);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint64_t x_34; lean_object* x_35; double x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
x_35 = lean_ctor_get(x_12, 0);
lean_inc(x_35);
lean_dec(x_12);
x_36 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1;
x_37 = 0;
x_38 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_39 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_float(x_39, sizeof(void*)*2, x_36);
lean_ctor_set_float(x_39, sizeof(void*)*2 + 8, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 16, x_37);
x_40 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2;
x_41 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_8);
lean_ctor_set(x_41, 2, x_40);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_41);
lean_ctor_set(x_10, 0, x_6);
x_42 = l_Lean_PersistentArray_push___rarg(x_35, x_10);
x_43 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint64(x_43, sizeof(void*)*1, x_34);
lean_ctor_set(x_11, 3, x_43);
x_44 = lean_st_ref_set(x_4, x_11, x_14);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint64_t x_55; lean_object* x_56; lean_object* x_57; double x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
x_51 = lean_ctor_get(x_11, 2);
x_52 = lean_ctor_get(x_11, 4);
x_53 = lean_ctor_get(x_11, 5);
x_54 = lean_ctor_get(x_11, 6);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_55 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
x_56 = lean_ctor_get(x_12, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_57 = x_12;
} else {
 lean_dec_ref(x_12);
 x_57 = lean_box(0);
}
x_58 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1;
x_59 = 0;
x_60 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_61 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_float(x_61, sizeof(void*)*2, x_58);
lean_ctor_set_float(x_61, sizeof(void*)*2 + 8, x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*2 + 16, x_59);
x_62 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2;
x_63 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_8);
lean_ctor_set(x_63, 2, x_62);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_63);
lean_ctor_set(x_10, 0, x_6);
x_64 = l_Lean_PersistentArray_push___rarg(x_56, x_10);
if (lean_is_scalar(x_57)) {
 x_65 = lean_alloc_ctor(0, 1, 8);
} else {
 x_65 = x_57;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint64(x_65, sizeof(void*)*1, x_55);
x_66 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_50);
lean_ctor_set(x_66, 2, x_51);
lean_ctor_set(x_66, 3, x_65);
lean_ctor_set(x_66, 4, x_52);
lean_ctor_set(x_66, 5, x_53);
lean_ctor_set(x_66, 6, x_54);
x_67 = lean_st_ref_set(x_4, x_66, x_14);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; double x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_72 = lean_ctor_get(x_10, 1);
lean_inc(x_72);
lean_dec(x_10);
x_73 = lean_ctor_get(x_11, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_11, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_11, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_11, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_11, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_11, 6);
lean_inc(x_78);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 lean_ctor_release(x_11, 6);
 x_79 = x_11;
} else {
 lean_dec_ref(x_11);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
x_81 = lean_ctor_get(x_12, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_82 = x_12;
} else {
 lean_dec_ref(x_12);
 x_82 = lean_box(0);
}
x_83 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1;
x_84 = 0;
x_85 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_86 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set_float(x_86, sizeof(void*)*2, x_83);
lean_ctor_set_float(x_86, sizeof(void*)*2 + 8, x_83);
lean_ctor_set_uint8(x_86, sizeof(void*)*2 + 16, x_84);
x_87 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2;
x_88 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_8);
lean_ctor_set(x_88, 2, x_87);
lean_inc(x_6);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_6);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_PersistentArray_push___rarg(x_81, x_89);
if (lean_is_scalar(x_82)) {
 x_91 = lean_alloc_ctor(0, 1, 8);
} else {
 x_91 = x_82;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set_uint64(x_91, sizeof(void*)*1, x_80);
if (lean_is_scalar(x_79)) {
 x_92 = lean_alloc_ctor(0, 7, 0);
} else {
 x_92 = x_79;
}
lean_ctor_set(x_92, 0, x_73);
lean_ctor_set(x_92, 1, x_74);
lean_ctor_set(x_92, 2, x_75);
lean_ctor_set(x_92, 3, x_91);
lean_ctor_set(x_92, 4, x_76);
lean_ctor_set(x_92, 5, x_77);
lean_ctor_set(x_92, 6, x_78);
x_93 = lean_st_ref_set(x_4, x_92, x_72);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
x_96 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 1;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_format___lambda__2(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 10;
x_3 = lean_uint32_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_box(0);
x_10 = lean_apply_5(x_1, x_8, x_9, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("format: uncaught backtrack exception", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_format___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_format___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_pp_oneline;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_format___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" [...]", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Parser_getTokenTable(x_12);
lean_dec(x_12);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Syntax_Traverser_fromSyntax(x_1);
x_16 = l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1;
x_17 = 0;
x_18 = 1;
x_19 = l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2;
x_20 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 1, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*3 + 2, x_18);
x_35 = lean_st_mk_ref(x_20, x_10);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_PrettyPrinter_Formatter_concat___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_36);
x_39 = l_Lean_PrettyPrinter_Formatter_fold(x_38, x_2, x_14, x_36, x_4, x_5, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_get(x_36, x_40);
lean_dec(x_36);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 2);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_lt(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lean_PrettyPrinter_format___lambda__4___closed__3;
x_49 = l_Lean_PrettyPrinter_format___lambda__4___closed__4;
x_50 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_7, x_49);
if (x_47 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_44);
x_77 = l_Std_instInhabitedFormat;
x_78 = l_outOfBounds___rarg(x_77);
x_51 = x_78;
goto block_76;
}
else
{
lean_object* x_79; 
x_79 = lean_array_fget(x_44, x_46);
lean_dec(x_44);
x_51 = x_79;
goto block_76;
}
block_76:
{
if (x_50 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
x_52 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
x_53 = lean_apply_5(x_48, x_51, x_52, x_4, x_5, x_43);
if (lean_obj_tag(x_53) == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_21 = x_54;
x_22 = x_55;
goto block_34;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_inc(x_51);
x_56 = l_Std_Format_pretty_x27(x_51, x_7);
lean_dec(x_7);
x_57 = lean_string_utf8_byte_size(x_56);
x_58 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_56, x_57, x_46);
x_59 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_56, x_58, x_57);
x_60 = lean_string_utf8_extract(x_56, x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_56);
x_61 = lean_string_utf8_byte_size(x_60);
x_62 = l_Lean_PrettyPrinter_format___lambda__4___closed__5;
x_63 = l_String_findAux(x_60, x_62, x_61, x_46);
x_64 = lean_nat_dec_lt(x_63, x_61);
lean_dec(x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_63);
x_65 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
x_66 = l_Lean_PrettyPrinter_format___lambda__3(x_48, x_51, x_60, x_65, x_4, x_5, x_43);
lean_dec(x_51);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_21 = x_67;
x_22 = x_68;
goto block_34;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_string_utf8_extract(x_60, x_46, x_63);
lean_dec(x_63);
lean_dec(x_60);
x_70 = l_Lean_PrettyPrinter_format___lambda__4___closed__6;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
x_73 = l_Lean_PrettyPrinter_format___lambda__3(x_48, x_51, x_71, x_72, x_4, x_5, x_43);
lean_dec(x_51);
if (lean_obj_tag(x_73) == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_21 = x_74;
x_22 = x_75;
goto block_34;
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_36);
lean_dec(x_7);
x_80 = lean_ctor_get(x_39, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_39, 1);
lean_inc(x_81);
lean_dec(x_39);
x_21 = x_80;
x_22 = x_81;
goto block_34;
}
block_34:
{
uint8_t x_23; 
x_23 = l_Lean_Exception_isInterrupt(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_21);
if (x_24 == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_11)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_11;
 lean_ctor_set_tag(x_25, 1);
}
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1;
x_28 = lean_nat_dec_eq(x_27, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_11)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_11;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_11);
x_30 = l_Lean_PrettyPrinter_format___lambda__4___closed__2;
x_31 = l_Lean_throwError___at_Lean_PrettyPrinter_format___spec__1(x_30, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_11)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_11;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_11)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_11;
 lean_ctor_set_tag(x_33, 1);
}
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("input", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__1;
x_3 = l_Lean_PrettyPrinter_format___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_PrettyPrinter_format___closed__2;
x_7 = l_Lean_isTracingEnabledFor___at_Lean_compileDecl___spec__3(x_6, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = l_Lean_PrettyPrinter_format___lambda__4(x_2, x_1, x_11, x_3, x_4, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_19 = l_Lean_Syntax_formatStxAux(x_16, x_17, x_18, x_2);
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_20);
lean_ctor_set(x_7, 0, x_21);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__2(x_6, x_22, x_3, x_4, x_14);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_format___lambda__4(x_2, x_1, x_24, x_3, x_4, x_25);
lean_dec(x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_box(0);
x_29 = 0;
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_31 = l_Lean_Syntax_formatStxAux(x_28, x_29, x_30, x_2);
x_32 = l_Lean_MessageData_ofFormat(x_31);
x_33 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__2(x_6, x_35, x_3, x_4, x_27);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_PrettyPrinter_format___lambda__4(x_2, x_1, x_37, x_3, x_4, x_38);
lean_dec(x_37);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_format___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_PrettyPrinter_format___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at_Lean_PrettyPrinter_format___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PrettyPrinter_format___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_PrettyPrinter_format___lambda__2(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_format___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_format___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_format___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_categoryFormatter), 6, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_PrettyPrinter_format(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_formatTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_formatTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_formatTerm___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_formatTerm___closed__2;
x_6 = l_Lean_PrettyPrinter_formatCategory(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_formatTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_formatTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_formatTactic___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_formatTactic___closed__2;
x_6 = l_Lean_PrettyPrinter_formatCategory(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_formatCommand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_formatCommand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_formatCommand___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_formatCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_formatCommand___closed__2;
x_6 = l_Lean_PrettyPrinter_formatCategory(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__1;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__2;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__4;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__6;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__7;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__8;
x_2 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__9;
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__11;
x_2 = lean_unsigned_to_nat(5787u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__2;
x_3 = 0;
x_4 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__12;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_PrettyPrinter_Formatter_checkKind___closed__2;
x_8 = 1;
x_9 = l_Lean_registerTraceClass(x_7, x_8, x_4, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_format___closed__2;
x_12 = l_Lean_registerTraceClass(x_11, x_8, x_4, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_StrInterpolation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ParserCompiler_Attribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_StrInterpolation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler_Attribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1 = _init_l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_FormatterM_orElse___rarg___closed__1);
l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1 = _init_l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_instOrElseFormatterM___closed__1);
l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__1 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__1();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__1);
l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__2 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__2();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__2);
l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__3 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__3();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__3___closed__3);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__1 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__1);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__2 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__2);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__3 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__3);
l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___lambda__3___closed__4);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__1);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__2);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__3);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__4);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__5);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__7);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__8);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__9);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__10);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__11);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__12);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__13);
l_Lean_PrettyPrinter_mkFormatterAttribute___closed__14 = _init_l_Lean_PrettyPrinter_mkFormatterAttribute___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_mkFormatterAttribute___closed__14);
if (builtin) {res = l_Lean_PrettyPrinter_mkFormatterAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_formatterAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_formatterAttribute);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1 = _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__1);
l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2 = _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__2);
l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3 = _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__3);
l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__4 = _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__4);
l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__5 = _init_l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute___closed__5);
if (builtin) {res = l_Lean_PrettyPrinter_mkCombinatorFormatterAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_combinatorFormatterAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_combinatorFormatterAttribute);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_throwBacktrack___rarg___closed__1);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__1);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__2);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__3);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM___closed__4);
l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM = _init_l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_instMonadTraverserFormatterM);
l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_pushWhitespace___closed__1);
l_Lean_PrettyPrinter_Formatter_concat___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_concat___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_concat___closed__1);
l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_orelse_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__1);
l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__2);
l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__3);
l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__4);
l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__5);
l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe___closed__6);
l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__1___closed__1);
l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__1();
l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Formatter_categoryFormatterCore___spec__3___closed__2);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__1);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__2);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__3);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__4);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__5);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___lambda__5___closed__6);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__1);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__2);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__3);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__4);
l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_categoryFormatterCore___closed__5);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__1);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__2);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__3);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__4);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__5);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__6);
l_Lean_PrettyPrinter_Formatter_checkKind___closed__7 = _init_l_Lean_PrettyPrinter_Formatter_checkKind___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_checkKind___closed__7);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__1);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___lambda__1___closed__2);
l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_parseToken___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_parseToken___closed__1);
l_Lean_PrettyPrinter_Formatter_parseToken___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_parseToken___closed__2);
l_Lean_PrettyPrinter_Formatter_parseToken___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_parseToken___closed__3);
l_Lean_PrettyPrinter_Formatter_parseToken___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_parseToken___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_parseToken___closed__4);
l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__1);
l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__2);
l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__2___closed__3);
l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__1);
l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__2);
l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__3);
l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_pushToken___lambda__5___closed__4);
l_Lean_PrettyPrinter_Formatter_pushToken___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_pushToken___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_pushToken___closed__1);
l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__1 = _init_l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__1);
l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__2 = _init_l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__2);
l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__3 = _init_l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___spec__1___closed__3);
l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__3);
l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__4);
l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__5 = _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__5);
l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__6 = _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__6);
l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__7 = _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__7);
l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__8 = _init_l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter___closed__8);
l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_unicodeSymbolNoAntiquot_formatter___closed__3);
l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3 = _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__3);
l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4 = _init_l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_identNoAntiquot_formatter___closed__4);
l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_charLitNoAntiquot_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_strLitNoAntiquot_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_nameLitNoAntiquot_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_numLitNoAntiquot_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_scientificLitNoAntiquot_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_fieldIdx_formatter___closed__2);
l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__2 = _init_l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_many1Unbox_formatter___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___spec__1___closed__2);
l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___closed__1);
l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1 = _init_l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed__const__1);
if (builtin) {res = l_Lean_PrettyPrinter_Formatter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5205_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Formatter_formatterAliasesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_formatterAliasesRef);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_Formatter_registerAlias___closed__1 = _init_l_Lean_PrettyPrinter_Formatter_registerAlias___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Formatter_registerAlias___closed__1);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__1 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__1);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__2 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__2);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__3 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__3);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__4 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__4);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__5 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__5);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__6 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304____closed__6);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5304_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_pp_oneline = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_pp_oneline);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_format___lambda__4___closed__1 = _init_l_Lean_PrettyPrinter_format___lambda__4___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_format___lambda__4___closed__1);
l_Lean_PrettyPrinter_format___lambda__4___closed__2 = _init_l_Lean_PrettyPrinter_format___lambda__4___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_format___lambda__4___closed__2);
l_Lean_PrettyPrinter_format___lambda__4___closed__3 = _init_l_Lean_PrettyPrinter_format___lambda__4___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_format___lambda__4___closed__3);
l_Lean_PrettyPrinter_format___lambda__4___closed__4 = _init_l_Lean_PrettyPrinter_format___lambda__4___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_format___lambda__4___closed__4);
l_Lean_PrettyPrinter_format___lambda__4___closed__5 = _init_l_Lean_PrettyPrinter_format___lambda__4___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_format___lambda__4___closed__5);
l_Lean_PrettyPrinter_format___lambda__4___closed__6 = _init_l_Lean_PrettyPrinter_format___lambda__4___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_format___lambda__4___closed__6);
l_Lean_PrettyPrinter_format___closed__1 = _init_l_Lean_PrettyPrinter_format___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_format___closed__1);
l_Lean_PrettyPrinter_format___closed__2 = _init_l_Lean_PrettyPrinter_format___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_format___closed__2);
l_Lean_PrettyPrinter_formatTerm___closed__1 = _init_l_Lean_PrettyPrinter_formatTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_formatTerm___closed__1);
l_Lean_PrettyPrinter_formatTerm___closed__2 = _init_l_Lean_PrettyPrinter_formatTerm___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_formatTerm___closed__2);
l_Lean_PrettyPrinter_formatTactic___closed__1 = _init_l_Lean_PrettyPrinter_formatTactic___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_formatTactic___closed__1);
l_Lean_PrettyPrinter_formatTactic___closed__2 = _init_l_Lean_PrettyPrinter_formatTactic___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_formatTactic___closed__2);
l_Lean_PrettyPrinter_formatCommand___closed__1 = _init_l_Lean_PrettyPrinter_formatCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_formatCommand___closed__1);
l_Lean_PrettyPrinter_formatCommand___closed__2 = _init_l_Lean_PrettyPrinter_formatCommand___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_formatCommand___closed__2);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__1 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__1);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__2 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__2);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__3 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__3);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__4 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__4);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__5 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__5);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__6 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__6);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__7 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__7);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__8 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__8);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__9 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__9);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__10 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__10);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__11 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__11);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__12 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787____closed__12);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Formatter___hyg_5787_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
