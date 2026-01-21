// Lean compiler output
// Module: Init.Meta.Defs
// Imports: import all Init.Prelude public import Init.Syntax public import Init.Data.Array.GetLit public import Init.Data.Option.BasicAux public meta import Init.Data.Array.Basic public meta import Init.Syntax
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object*, lean_object*);
static lean_object* l_Lean_Name_reprPrec___closed__7;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t);
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_quoteNameMk___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8;
static lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instBEq___closed__0;
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeNumLitTerm;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2;
static lean_object* l_Lean_Syntax_instRepr_repr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37;
static lean_object* l_Lean_Name_isInaccessibleUserName___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx___boxed(lean_object*);
lean_object* lean_version_get_patch(lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__5;
static lean_object* l_Array_getSepElems___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_githash;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object*);
static lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0;
static uint8_t l_Lean_versionString___closed__1;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object*, uint8_t);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr;
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object*);
static lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_instRepr;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__30;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object*);
static lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__3;
static lean_object* l_Lean_Name_reprPrec___closed__5;
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__5;
LEAN_EXPORT lean_object* lean_name_append_after(lean_object*, lean_object*);
static lean_object* l_Lean_TSyntax_getScientific___closed__1;
static lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
static lean_object* l_Lean_versionString___closed__4;
uint8_t l_Array_isEmpty___redArg(lean_object*);
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
static lean_object* l_Lean_Syntax_mkScientificLit___closed__0;
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t, lean_object*);
static lean_object* l_Lean_versionString___closed__7;
static lean_object* l_Lean_Syntax_mkNumLit___closed__1;
lean_object* l_Std_Format_fill(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeNumLitPrec;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11;
static lean_object* l_Lean_Syntax_instReprPreresolved___closed__0;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_origin;
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeStrLitTerm;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__2;
static lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__0;
static lean_object* l_Array_getSepElems___redArg___closed__1;
static uint8_t l_Lean_version_isRelease___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object*);
static lean_object* l_Lean_Syntax_isFieldIdx_x3f___closed__1;
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__4;
static lean_object* l_Lean_mkHole___closed__1;
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprEtaStructMode___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31;
lean_object* lean_substring_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object*, lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__14;
static lean_object* l_Lean_Syntax_SepArray_ofElems___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__38;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__15;
lean_object* lean_string_trim(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
static lean_object* l_Lean_instQuoteBoolMkStr1___closed__0;
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2;
static lean_object* l_Lean_instQuoteStringStrLitKind___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_version_major___closed__0;
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object*);
static lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object*);
static lean_object* l_Lean_Syntax_mkNumLit___closed__0;
LEAN_EXPORT uint8_t l_Lean_isGreek(uint32_t);
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object*);
static lean_object* l_Lean_Syntax_instRepr_repr___closed__8;
static lean_object* l_Lean_version_specialDesc___closed__0;
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteTermMkStr1;
static lean_object* l_Lean_Name_reprPrec___closed__0;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instRepr_repr___closed__2;
static lean_object* l_Lean_mkCIdentFrom___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__26;
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object*);
static lean_object* l_Array_getSepElems___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__39;
static lean_object* l_Lean_mkOptionalNode___closed__0;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_versionString___closed__0;
static lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0;
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint32_t l_Lean_idBeginEscape;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isGreek___boxed(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_substring_front(lean_object*);
static lean_object* l_Lean_quoteNameMk___closed__0;
static lean_object* l_Lean_versionString___closed__6;
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__0;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instQuoteTermMkStr1___closed__0;
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object*);
static lean_object* l_Lean_versionStringCore___closed__0;
LEAN_EXPORT lean_object* lean_name_append_before(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode;
static lean_object* l_Lean_TSyntax_getScientific___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object*, lean_object*);
uint8_t lean_string_isprefixof(lean_object*, lean_object*);
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__3;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__0;
LEAN_EXPORT uint8_t l_Lean_version_isRelease;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_instQuoteRawMkStr1___closed__0;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__12;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instQuoteNatNumLitKind___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_expandMacros___lam__0___closed__4;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_mkCharLit___closed__0;
static lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__28;
static lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instRepr_repr___closed__11;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object*);
static lean_object* l_Lean_versionStringCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__1;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved;
static lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__1;
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0;
static lean_object* l_Lean_versionStringCore___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_mkCharLit___closed__1;
uint8_t lean_string_contains(lean_object*, uint32_t);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_mkOptionalNode___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1;
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__31;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig;
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toolchain;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4;
static lean_object* l_Lean_Syntax_instRepr_repr___closed__3;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1;
static lean_object* l_Lean_Syntax_SepArray_ofElems___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_substring_takewhile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1;
static lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2;
static lean_object* l_Lean_expandMacros___lam__0___closed__0;
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object*);
static lean_object* l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2;
static lean_object* l_Lean_instQuoteNameMkStr1___private__1___closed__0;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode;
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0;
lean_object* l_instReprSourceInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_mkApp___closed__0;
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__22;
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0;
static lean_object* l_Lean_Meta_instReprTransparencyMode___closed__0;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__6;
static lean_object* l_Lean_quoteNameMk___closed__6;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0;
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__0;
static uint8_t l_Lean_isIdFirstAscii___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
static lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__4;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4;
uint8_t lean_substring_beq(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object*);
static lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__2;
static lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__6;
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versionString;
static lean_object* l_Array_getSepElems___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_versionString___closed__2;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__23;
static lean_object* l_Lean_Name_reprPrec___closed__9;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__35;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkSepArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23;
static lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0;
static lean_object* l_Lean_versionStringCore___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__3;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_instQuoteNameMkStr1___private__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_getGithash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_mkGroupNode___closed__0;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__12;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lean_isIdRestAscii___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
static lean_object* l_Lean_Name_reprPrec___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object*);
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2;
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__4;
static lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___closed__0;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Char_quote(uint32_t);
static lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object*, lean_object*);
uint8_t lean_substring_isempty(lean_object*);
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkOptionalNode___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1;
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__16;
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_mkApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object*, lean_object*);
static lean_object* l_Lean_versionString___closed__3;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28;
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutSepArrayArray(lean_object*);
static lean_object* l_Lean_Name_reprPrec___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_substring_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__15;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_substring_prev(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__8;
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeNumLitPrio;
static lean_object* l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__13;
static lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__2;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__0;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentLevel;
static lean_object* l_Lean_quoteNameMk___closed__5;
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Name_instRepr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_isStage0___boxed(lean_object*);
uint8_t lean_version_get_is_release(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__2;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_version_minor;
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object*);
static lean_object* l_Lean_Syntax_instRepr_repr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27;
static lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object*);
static lean_object* l_Lean_instQuoteNameMkStr1___closed__0;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object*);
static lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__5;
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_version_get_special_desc(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__2;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeScientificLitTerm;
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object*, lean_object*);
lean_object* lean_string_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1;
LEAN_EXPORT lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object*);
static lean_object* l_Lean_versionString___closed__5;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object*);
static lean_object* l_Lean_Syntax_instRepr_repr___closed__5;
static lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object*, lean_object*);
static lean_object* l_Lean_toolchain___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object*);
static lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2;
lean_object* l_Lean_MacroScopesView_review(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__33;
static lean_object* l_Lean_expandMacros___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__5;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0;
lean_object* l_String_toRawSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_githash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0;
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_version_major;
static lean_object* l_Lean_Syntax_instRepr_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
static lean_object* l_Lean_Syntax_instRepr_repr___closed__10;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__36;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__7;
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object*, lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2;
static lean_object* l_Lean_origin___closed__0;
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isLetterLike(uint32_t);
lean_object* lean_substring_tostring(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t lean_substring_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0;
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t, uint8_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__6;
static lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object*);
static lean_object* l_Lean_Syntax_decodeStringGap___closed__0;
static lean_object* l_Lean_quoteNameMk___closed__2;
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0;
static lean_object* l_Lean_Name_reprPrec___closed__6;
static lean_object* l_Lean_toolchain___closed__2;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12;
static lean_object* l_Array_getSepElems___redArg___closed__5;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__24;
LEAN_EXPORT uint32_t l_Lean_idEndEscape;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t);
static lean_object* l_Lean_toolchain___closed__0;
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__0;
static lean_object* l_Lean_Name_reprPrec___closed__3;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__27;
static lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__4;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__10;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__1;
static lean_object* l_Lean_version_patch___closed__0;
lean_object* lean_version_get_minor(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object*, lean_object*);
uint8_t lean_internal_is_stage0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object*);
static lean_object* l_Lean_evalPrio___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object*);
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__17;
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__37;
static lean_object* l_Lean_Meta_instReprEtaStructMode_repr___closed__1;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMinor___boxed(lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__9;
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1___closed__0;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32;
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_TSyntaxArray_mkImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_string_pos_min(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Internal_hasLLVMBackend___boxed(lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__13;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static uint8_t l_Lean_isIdRestAscii___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__0;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkHole___closed__0;
LEAN_EXPORT lean_object* l_Lean_version_patch;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33;
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object*, lean_object*);
static lean_object* l_Array_getSepElems___redArg___closed__10;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__16;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object*);
static lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1;
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__6;
LEAN_EXPORT lean_object* l_String_toName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_quoteNameMk___closed__1;
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object*);
static lean_object* l_Lean_Syntax_isFieldIdx_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1;
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_nextwhile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_mkNameLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20;
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkSepArray___closed__1;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instRepr_repr___closed__4;
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2;
static lean_object* l_Lean_Syntax_mkStrLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_versionStringCore;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object*);
static lean_object* l_Lean_version_minor___closed__0;
static lean_object* l_Lean_Meta_instReprConfig___closed__0;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeNameLitTerm;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13;
static lean_object* l_Lean_expandMacros___closed__0;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5;
static lean_object* l_Array_getSepElems___redArg___closed__7;
static lean_object* l_Lean_Name_reprPrec___closed__4;
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__10;
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instRepr_repr___closed__9;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_inaccessible_user_name(lean_object*);
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__32;
static lean_object* l_Lean_instQuoteRawMkStr1___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeCharLitTerm;
static lean_object* l_Lean_versionStringCore___closed__7;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35;
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10;
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__5;
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Array_getSepElems___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instReprPreresolved_repr___closed__2;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__25;
static lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0;
lean_object* l_Lean_SourceInfo_getTrailing_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t);
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object*);
uint8_t lean_internal_has_llvm_backend(lean_object*);
uint32_t lean_string_front(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3;
static lean_object* l_Lean_versionStringCore___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3;
lean_object* lean_version_get_major(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMajor___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instRepr___closed__0;
static uint8_t l_Lean_isIdRestAscii___closed__2;
lean_object* lean_string_intercalate(lean_object*, lean_object*);
static uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7;
static lean_object* l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1;
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkCIdentFrom___closed__1;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object*);
static lean_object* l_Array_getSepElems___redArg___closed__3;
uint8_t lean_string_isempty(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_version_getSpecialDesc___boxed(lean_object*);
static lean_object* l_Lean_mkOptionalNode___closed__3;
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Syntax_instRepr_repr___closed__1;
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object*);
static lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6;
static lean_object* l_Lean_Option_hasQuote___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_versionStringCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__9;
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__20;
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object*);
static lean_object* l_Lean_quoteNameMk___closed__4;
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object*);
static lean_object* l_Lean_toolchain___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprTransparencyMode_repr___closed__8;
static lean_object* l_Lean_Syntax_mkStrLit___closed__0;
static lean_object* l_Lean_quoteNameMk___closed__3;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_expandMacros___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Name_reprPrec___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getPatch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t, lean_object*);
lean_object* lean_nat_pred(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_TSyntax_expandInterpolatedStr___closed__11;
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24;
static lean_object* l_Array_getSepElems___redArg___closed__4;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Parser_Tactic_getConfigItems___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_expandMacros___lam__0___closed__1;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l_Lean_mkGroupNode___closed__1;
lean_object* lean_string_dropright(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0;
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36;
static lean_object* l_Lean_Syntax_mkScientificLit___closed__1;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10;
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeArraySepArray(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object*, lean_object*);
static lean_object* l_Lean_evalPrec___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_githash___closed__0;
static lean_object* l_Array_getSepElems___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_toolchain___closed__4;
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_version_getIsRelease___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTermTSyntaxConsSyntaxNodeKindMkStr4Nil;
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object*, lean_object*);
static lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__4;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__21;
static lean_object* l_Lean_instQuoteCharCharLitKind___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__34;
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29;
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_version_specialDesc;
static lean_object* l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEq;
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__3;
static lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___closed__2;
uint8_t lean_string_any(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instBEqPreresolved___closed__0;
static lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__19;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_pos_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object*);
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__29;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_toolchain___closed__1;
uint32_t l_Char_ofNat(lean_object*);
static lean_object* l_Lean_TSyntax_instCoeIdentTerm___closed__0;
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14;
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0;
uint32_t lean_substring_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
static lean_object* l_Lean_versionStringCore___closed__6;
static lean_object* l_Lean_Syntax_mkNameLit___closed__0;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object*);
static lean_object* l_Lean_Syntax_getHead_x3f___closed__0;
static lean_object* l_Lean_Meta_instReprConfig_repr___redArg___closed__17;
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object*);
static lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* lean_string_capitalize(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMajor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_version_get_major(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_version_major___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_version_get_major(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_version_major() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_version_major___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getMinor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_version_get_minor(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_version_minor___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_version_get_minor(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_version_minor() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_version_minor___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_version_getPatch___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_version_get_patch(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_version_patch___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_version_get_patch(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_version_patch() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_version_patch___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_getGithash___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_githash(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_githash___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_githash(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_githash() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_githash___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_version_getIsRelease___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_version_get_is_release(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static uint8_t _init_l_Lean_version_isRelease___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_version_get_is_release(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_version_isRelease() {
_start:
{
uint8_t x_1; 
x_1 = l_Lean_version_isRelease___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_version_getSpecialDesc___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_version_get_special_desc(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_version_specialDesc___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_version_get_special_desc(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_version_specialDesc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_version_specialDesc___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_version_major;
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionStringCore___closed__1;
x_2 = l_Lean_versionStringCore___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_version_minor;
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionStringCore___closed__3;
x_2 = l_Lean_versionStringCore___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionStringCore___closed__1;
x_2 = l_Lean_versionStringCore___closed__4;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_version_patch;
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_versionStringCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionStringCore___closed__6;
x_2 = l_Lean_versionStringCore___closed__5;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_versionStringCore() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_versionStringCore___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_versionString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static uint8_t _init_l_Lean_versionString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_versionString___closed__0;
x_2 = l_Lean_version_specialDesc;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_versionString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_versionString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionString___closed__2;
x_2 = l_Lean_versionStringCore;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_versionString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_version_specialDesc;
x_2 = l_Lean_versionString___closed__3;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_versionString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", commit ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_versionString___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionString___closed__5;
x_2 = l_Lean_versionStringCore;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_versionString___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_githash;
x_2 = l_Lean_versionString___closed__6;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_versionString() {
_start:
{
uint8_t x_1; 
x_1 = l_Lean_versionString___closed__1;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_versionString___closed__4;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = l_Lean_version_isRelease;
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_versionString___closed__7;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_versionStringCore;
return x_5;
}
}
}
}
static lean_object* _init_l_Lean_origin___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanprover/lean4", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_origin() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_origin___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_toolchain___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_toolchain___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_toolchain___closed__0;
x_2 = l_Lean_origin___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_toolchain___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_version_specialDesc;
x_2 = l_Lean_toolchain___closed__1;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_toolchain___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionStringCore;
x_2 = l_Lean_toolchain___closed__1;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_toolchain___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_versionString___closed__2;
x_2 = l_Lean_toolchain___closed__3;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_toolchain___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_version_specialDesc;
x_2 = l_Lean_toolchain___closed__4;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_toolchain() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_versionString___closed__0;
x_2 = l_Lean_versionString___closed__1;
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_version_isRelease;
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_toolchain___closed__2;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_toolchain___closed__5;
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = l_Lean_version_isRelease;
if (x_6 == 0)
{
return x_1;
}
else
{
lean_object* x_7; 
x_7 = l_Lean_toolchain___closed__3;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_isStage0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_is_stage0(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Internal_hasLLVMBackend___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_has_llvm_backend(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_isGreek(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 913;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 989;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isGreek___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isGreek(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isLetterLike(uint32_t x_1) {
_start:
{
uint8_t x_7; uint8_t x_13; uint8_t x_19; uint8_t x_25; uint8_t x_31; uint8_t x_42; uint8_t x_53; uint32_t x_57; uint8_t x_58; 
x_57 = 945;
x_58 = lean_uint32_dec_le(x_57, x_1);
if (x_58 == 0)
{
x_53 = x_58;
goto block_56;
}
else
{
uint32_t x_59; uint8_t x_60; 
x_59 = 969;
x_60 = lean_uint32_dec_le(x_1, x_59);
x_53 = x_60;
goto block_56;
}
block_6:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 256;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 383;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
block_12:
{
if (x_7 == 0)
{
goto block_6;
}
else
{
uint32_t x_8; uint8_t x_9; 
x_8 = 215;
x_9 = lean_uint32_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 247;
x_11 = lean_uint32_dec_eq(x_1, x_10);
if (x_11 == 0)
{
return x_7;
}
else
{
goto block_6;
}
}
else
{
goto block_6;
}
}
}
block_18:
{
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 192;
x_15 = lean_uint32_dec_le(x_14, x_1);
if (x_15 == 0)
{
x_7 = x_15;
goto block_12;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 255;
x_17 = lean_uint32_dec_le(x_1, x_16);
x_7 = x_17;
goto block_12;
}
}
else
{
return x_13;
}
}
block_24:
{
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 119964;
x_21 = lean_uint32_dec_le(x_20, x_1);
if (x_21 == 0)
{
x_13 = x_21;
goto block_18;
}
else
{
uint32_t x_22; uint8_t x_23; 
x_22 = 120223;
x_23 = lean_uint32_dec_le(x_1, x_22);
x_13 = x_23;
goto block_18;
}
}
else
{
return x_19;
}
}
block_30:
{
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 8448;
x_27 = lean_uint32_dec_le(x_26, x_1);
if (x_27 == 0)
{
x_19 = x_27;
goto block_24;
}
else
{
uint32_t x_28; uint8_t x_29; 
x_28 = 8527;
x_29 = lean_uint32_dec_le(x_1, x_28);
x_19 = x_29;
goto block_24;
}
}
else
{
return x_25;
}
}
block_36:
{
if (x_31 == 0)
{
uint32_t x_32; uint8_t x_33; 
x_32 = 7936;
x_33 = lean_uint32_dec_le(x_32, x_1);
if (x_33 == 0)
{
x_25 = x_33;
goto block_30;
}
else
{
uint32_t x_34; uint8_t x_35; 
x_34 = 8190;
x_35 = lean_uint32_dec_le(x_1, x_34);
x_25 = x_35;
goto block_30;
}
}
else
{
return x_31;
}
}
block_41:
{
uint32_t x_37; uint8_t x_38; 
x_37 = 970;
x_38 = lean_uint32_dec_le(x_37, x_1);
if (x_38 == 0)
{
x_31 = x_38;
goto block_36;
}
else
{
uint32_t x_39; uint8_t x_40; 
x_39 = 1019;
x_40 = lean_uint32_dec_le(x_1, x_39);
x_31 = x_40;
goto block_36;
}
}
block_47:
{
if (x_42 == 0)
{
goto block_41;
}
else
{
uint32_t x_43; uint8_t x_44; 
x_43 = 928;
x_44 = lean_uint32_dec_eq(x_1, x_43);
if (x_44 == 0)
{
uint32_t x_45; uint8_t x_46; 
x_45 = 931;
x_46 = lean_uint32_dec_eq(x_1, x_45);
if (x_46 == 0)
{
return x_42;
}
else
{
goto block_41;
}
}
else
{
goto block_41;
}
}
}
block_52:
{
uint32_t x_48; uint8_t x_49; 
x_48 = 913;
x_49 = lean_uint32_dec_le(x_48, x_1);
if (x_49 == 0)
{
x_42 = x_49;
goto block_47;
}
else
{
uint32_t x_50; uint8_t x_51; 
x_50 = 937;
x_51 = lean_uint32_dec_le(x_1, x_50);
x_42 = x_51;
goto block_47;
}
}
block_56:
{
if (x_53 == 0)
{
goto block_52;
}
else
{
uint32_t x_54; uint8_t x_55; 
x_54 = 955;
x_55 = lean_uint32_dec_eq(x_1, x_54);
if (x_55 == 0)
{
return x_53;
}
else
{
goto block_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLetterLike___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isLetterLike(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isNumericSubscript(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 8320;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 8329;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isNumericSubscript___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isNumericSubscript(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isSubScriptAlnum(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_6; uint8_t x_12; uint32_t x_18; uint8_t x_19; 
x_18 = 8320;
x_19 = lean_uint32_dec_le(x_18, x_1);
if (x_19 == 0)
{
x_12 = x_19;
goto block_17;
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 8329;
x_21 = lean_uint32_dec_le(x_1, x_20);
x_12 = x_21;
goto block_17;
}
block_5:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 11388;
x_4 = lean_uint32_dec_eq(x_1, x_3);
return x_4;
}
else
{
return x_2;
}
}
block_11:
{
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 7522;
x_8 = lean_uint32_dec_le(x_7, x_1);
if (x_8 == 0)
{
x_2 = x_8;
goto block_5;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 7530;
x_10 = lean_uint32_dec_le(x_1, x_9);
x_2 = x_10;
goto block_5;
}
}
else
{
return x_6;
}
}
block_17:
{
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 8336;
x_14 = lean_uint32_dec_le(x_13, x_1);
if (x_14 == 0)
{
x_6 = x_14;
goto block_11;
}
else
{
uint32_t x_15; uint8_t x_16; 
x_15 = 8348;
x_16 = lean_uint32_dec_le(x_1, x_15);
x_6 = x_16;
goto block_11;
}
}
else
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isSubScriptAlnum(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirst(uint32_t x_1) {
_start:
{
uint8_t x_2; uint32_t x_12; uint8_t x_13; 
x_12 = 65;
x_13 = lean_uint32_dec_le(x_12, x_1);
if (x_13 == 0)
{
goto block_11;
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 90;
x_15 = lean_uint32_dec_le(x_1, x_14);
if (x_15 == 0)
{
goto block_11;
}
else
{
return x_15;
}
}
block_6:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 95;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_isLetterLike(x_1);
return x_5;
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_11:
{
uint32_t x_7; uint8_t x_8; 
x_7 = 97;
x_8 = lean_uint32_dec_le(x_7, x_1);
if (x_8 == 0)
{
x_2 = x_8;
goto block_6;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 122;
x_10 = lean_uint32_dec_le(x_1, x_9);
x_2 = x_10;
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirst___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdFirst(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 65;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 90;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 97;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 122;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint8_t x_9; 
x_8 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_9 = lean_uint8_dec_le(x_8, x_1);
if (x_9 == 0)
{
x_2 = x_9;
goto block_7;
}
else
{
uint8_t x_10; uint8_t x_11; 
x_10 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_11 = lean_uint8_dec_le(x_1, x_10);
x_2 = x_11;
goto block_7;
}
block_7:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_4 = lean_uint8_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_4;
}
else
{
uint8_t x_5; uint8_t x_6; 
x_5 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_6 = lean_uint8_dec_le(x_1, x_5);
return x_6;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Lean_isIdFirstAscii___closed__0() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 95;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdFirstAscii(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_6; uint8_t x_12; uint8_t x_13; 
x_12 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_13 = lean_uint8_dec_le(x_12, x_1);
if (x_13 == 0)
{
x_6 = x_13;
goto block_11;
}
else
{
uint8_t x_14; uint8_t x_15; 
x_14 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_15 = lean_uint8_dec_le(x_1, x_14);
x_6 = x_15;
goto block_11;
}
block_5:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = l_Lean_isIdFirstAscii___closed__0;
x_4 = lean_uint8_dec_eq(x_1, x_3);
return x_4;
}
else
{
return x_2;
}
}
block_11:
{
if (x_6 == 0)
{
uint8_t x_7; uint8_t x_8; 
x_7 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_8 = lean_uint8_dec_le(x_7, x_1);
if (x_8 == 0)
{
x_2 = x_8;
goto block_5;
}
else
{
uint8_t x_9; uint8_t x_10; 
x_9 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_10 = lean_uint8_dec_le(x_1, x_9);
x_2 = x_10;
goto block_5;
}
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdFirstAscii___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_isIdFirstAscii(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 48;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 57;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint8_t x_14; uint8_t x_15; 
x_14 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_15 = lean_uint8_dec_le(x_14, x_1);
if (x_15 == 0)
{
x_8 = x_15;
goto block_13;
}
else
{
uint8_t x_16; uint8_t x_17; 
x_16 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_17 = lean_uint8_dec_le(x_1, x_16);
x_8 = x_17;
goto block_13;
}
block_7:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0;
x_4 = lean_uint8_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_4;
}
else
{
uint8_t x_5; uint8_t x_6; 
x_5 = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1;
x_6 = lean_uint8_dec_le(x_1, x_5);
return x_6;
}
}
else
{
return x_2;
}
}
block_13:
{
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_10 = lean_uint8_dec_le(x_9, x_1);
if (x_10 == 0)
{
x_2 = x_10;
goto block_7;
}
else
{
uint8_t x_11; uint8_t x_12; 
x_11 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_12 = lean_uint8_dec_le(x_1, x_11);
x_2 = x_12;
goto block_7;
}
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRest(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_14; uint32_t x_25; uint8_t x_26; 
x_25 = 65;
x_26 = lean_uint32_dec_le(x_25, x_1);
if (x_26 == 0)
{
goto block_24;
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = 90;
x_28 = lean_uint32_dec_le(x_1, x_27);
if (x_28 == 0)
{
goto block_24;
}
else
{
return x_28;
}
}
block_13:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 95;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 39;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 33;
x_8 = lean_uint32_dec_eq(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 63;
x_10 = lean_uint32_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_isLetterLike(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isSubScriptAlnum(x_1);
return x_12;
}
else
{
return x_11;
}
}
else
{
return x_10;
}
}
else
{
return x_8;
}
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_19:
{
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 48;
x_16 = lean_uint32_dec_le(x_15, x_1);
if (x_16 == 0)
{
x_2 = x_16;
goto block_13;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 57;
x_18 = lean_uint32_dec_le(x_1, x_17);
x_2 = x_18;
goto block_13;
}
}
else
{
return x_14;
}
}
block_24:
{
uint32_t x_20; uint8_t x_21; 
x_20 = 97;
x_21 = lean_uint32_dec_le(x_20, x_1);
if (x_21 == 0)
{
x_14 = x_21;
goto block_19;
}
else
{
uint32_t x_22; uint8_t x_23; 
x_22 = 122;
x_23 = lean_uint32_dec_le(x_1, x_22);
x_14 = x_23;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRest___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdRest(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__0() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 39;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__1() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 33;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_isIdRestAscii___closed__2() {
_start:
{
uint32_t x_1; uint8_t x_2; 
x_1 = 63;
x_2 = lean_uint32_to_uint8(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdRestAscii(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_12; uint8_t x_18; uint8_t x_24; uint8_t x_25; 
x_24 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_25 = lean_uint8_dec_le(x_24, x_1);
if (x_25 == 0)
{
x_18 = x_25;
goto block_23;
}
else
{
uint8_t x_26; uint8_t x_27; 
x_26 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_27 = lean_uint8_dec_le(x_1, x_26);
x_18 = x_27;
goto block_23;
}
block_11:
{
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; 
x_3 = l_Lean_isIdFirstAscii___closed__0;
x_4 = lean_uint8_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; 
x_5 = l_Lean_isIdRestAscii___closed__0;
x_6 = lean_uint8_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; uint8_t x_8; 
x_7 = l_Lean_isIdRestAscii___closed__1;
x_8 = lean_uint8_dec_eq(x_1, x_7);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = l_Lean_isIdRestAscii___closed__2;
x_10 = lean_uint8_dec_eq(x_1, x_9);
return x_10;
}
else
{
return x_8;
}
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_17:
{
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; 
x_13 = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0;
x_14 = lean_uint8_dec_le(x_13, x_1);
if (x_14 == 0)
{
x_2 = x_14;
goto block_11;
}
else
{
uint8_t x_15; uint8_t x_16; 
x_15 = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1;
x_16 = lean_uint8_dec_le(x_1, x_15);
x_2 = x_16;
goto block_11;
}
}
else
{
return x_12;
}
}
block_23:
{
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; 
x_19 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_20 = lean_uint8_dec_le(x_19, x_1);
if (x_20 == 0)
{
x_12 = x_20;
goto block_17;
}
else
{
uint8_t x_21; uint8_t x_22; 
x_21 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_22 = lean_uint8_dec_le(x_1, x_21);
x_12 = x_22;
goto block_17;
}
}
else
{
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIdRestAscii___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_isIdRestAscii(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint32_t _init_l_Lean_idBeginEscape() {
_start:
{
uint32_t x_1; 
x_1 = 171;
return x_1;
}
}
static uint32_t _init_l_Lean_idEndEscape() {
_start:
{
uint32_t x_1; 
x_1 = 187;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdBeginEscape(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 171;
x_3 = lean_uint32_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdBeginEscape(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_isIdEndEscape(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 187;
x_3 = lean_uint32_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isIdEndEscape___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_isIdEndEscape(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
x_1 = x_2;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_getRoot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Name_getRoot(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Name_isInaccessibleUserName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inaccessible", 13, 13);
return x_1;
}
}
LEAN_EXPORT uint8_t lean_is_inaccessible_user_name(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = 10013;
lean_inc_ref(x_2);
x_4 = lean_string_contains(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Name_isInaccessibleUserName___closed__0;
x_6 = lean_string_dec_eq(x_2, x_5);
lean_dec_ref(x_2);
return x_6;
}
else
{
lean_dec_ref(x_2);
return x_4;
}
}
case 2:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_1 = x_7;
goto _start;
}
default: 
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = 0;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_isInaccessibleUserName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_inaccessible_user_name(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_7; lean_object* x_9; uint8_t x_10; 
x_9 = lean_string_utf8_byte_size(x_1);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; uint8_t x_13; uint8_t x_23; uint8_t x_29; uint8_t x_35; uint8_t x_36; 
lean_inc(x_2);
x_12 = lean_string_get_byte_fast(x_1, x_2);
x_35 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_36 = lean_uint8_dec_le(x_35, x_12);
if (x_36 == 0)
{
x_29 = x_36;
goto block_34;
}
else
{
uint8_t x_37; uint8_t x_38; 
x_37 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_38 = lean_uint8_dec_le(x_12, x_37);
x_29 = x_38;
goto block_34;
}
block_22:
{
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; 
x_14 = l_Lean_isIdFirstAscii___closed__0;
x_15 = lean_uint8_dec_eq(x_12, x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; 
x_16 = l_Lean_isIdRestAscii___closed__0;
x_17 = lean_uint8_dec_eq(x_12, x_16);
if (x_17 == 0)
{
uint8_t x_18; uint8_t x_19; 
x_18 = l_Lean_isIdRestAscii___closed__1;
x_19 = lean_uint8_dec_eq(x_12, x_18);
if (x_19 == 0)
{
uint8_t x_20; uint8_t x_21; 
x_20 = l_Lean_isIdRestAscii___closed__2;
x_21 = lean_uint8_dec_eq(x_12, x_20);
x_7 = x_21;
goto block_8;
}
else
{
x_7 = x_19;
goto block_8;
}
}
else
{
x_7 = x_17;
goto block_8;
}
}
else
{
x_7 = x_15;
goto block_8;
}
}
else
{
goto block_6;
}
}
block_28:
{
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; 
x_24 = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0;
x_25 = lean_uint8_dec_le(x_24, x_12);
if (x_25 == 0)
{
x_13 = x_25;
goto block_22;
}
else
{
uint8_t x_26; uint8_t x_27; 
x_26 = l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1;
x_27 = lean_uint8_dec_le(x_12, x_26);
x_13 = x_27;
goto block_22;
}
}
else
{
goto block_6;
}
}
block_34:
{
if (x_29 == 0)
{
uint8_t x_30; uint8_t x_31; 
x_30 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_31 = lean_uint8_dec_le(x_30, x_12);
if (x_31 == 0)
{
x_23 = x_31;
goto block_28;
}
else
{
uint8_t x_32; uint8_t x_33; 
x_32 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_33 = lean_uint8_dec_le(x_12, x_32);
x_23 = x_33;
goto block_28;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
x_2 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
lean_dec(x_2);
return x_7;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(lean_object* x_1) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_11; uint8_t x_17; uint8_t x_18; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_get_byte_fast(x_1, x_5);
x_17 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_18 = lean_uint8_dec_le(x_17, x_6);
if (x_18 == 0)
{
x_11 = x_18;
goto block_16;
}
else
{
uint8_t x_19; uint8_t x_20; 
x_19 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_20 = lean_uint8_dec_le(x_6, x_19);
x_11 = x_20;
goto block_16;
}
block_4:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(x_1, x_2);
return x_3;
}
block_10:
{
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; 
x_8 = l_Lean_isIdFirstAscii___closed__0;
x_9 = lean_uint8_dec_eq(x_6, x_8);
if (x_9 == 0)
{
return x_9;
}
else
{
goto block_4;
}
}
else
{
goto block_4;
}
}
block_16:
{
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; 
x_12 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_13 = lean_uint8_dec_le(x_12, x_6);
if (x_13 == 0)
{
x_7 = x_13;
goto block_10;
}
else
{
uint8_t x_14; uint8_t x_15; 
x_14 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_15 = lean_uint8_dec_le(x_6, x_14);
x_7 = x_15;
goto block_10;
}
}
else
{
goto block_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_12; uint8_t x_18; uint8_t x_19; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_string_get_byte_fast(x_1, x_6);
x_18 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_19 = lean_uint8_dec_le(x_18, x_7);
if (x_19 == 0)
{
x_12 = x_19;
goto block_17;
}
else
{
uint8_t x_20; uint8_t x_21; 
x_20 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_21 = lean_uint8_dec_le(x_7, x_20);
x_12 = x_21;
goto block_17;
}
block_5:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(x_1, x_3);
return x_4;
}
block_11:
{
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = l_Lean_isIdFirstAscii___closed__0;
x_10 = lean_uint8_dec_eq(x_7, x_9);
if (x_10 == 0)
{
return x_10;
}
else
{
goto block_5;
}
}
else
{
goto block_5;
}
}
block_17:
{
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; 
x_13 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_14 = lean_uint8_dec_le(x_13, x_7);
if (x_14 == 0)
{
x_8 = x_14;
goto block_11;
}
else
{
uint8_t x_15; uint8_t x_16; 
x_15 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_16 = lean_uint8_dec_le(x_7, x_15);
x_8 = x_16;
goto block_11;
}
}
else
{
goto block_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAscii(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_isIdRest___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(lean_object* x_1) {
_start:
{
uint8_t x_10; uint32_t x_12; uint8_t x_13; uint32_t x_18; uint8_t x_24; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_41; uint8_t x_47; uint8_t x_48; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_string_get_byte_fast(x_1, x_35);
x_47 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_48 = lean_uint8_dec_le(x_47, x_36);
if (x_48 == 0)
{
x_41 = x_48;
goto block_46;
}
else
{
uint8_t x_49; uint8_t x_50; 
x_49 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_50 = lean_uint8_dec_le(x_36, x_49);
x_41 = x_50;
goto block_46;
}
block_9:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_substring_drop(x_4, x_5);
x_7 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0;
x_8 = lean_substring_all(x_6, x_7);
return x_8;
}
block_11:
{
if (x_10 == 0)
{
lean_dec_ref(x_1);
return x_10;
}
else
{
goto block_9;
}
}
block_17:
{
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 95;
x_15 = lean_uint32_dec_eq(x_12, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_isLetterLike(x_12);
x_10 = x_16;
goto block_11;
}
else
{
x_10 = x_15;
goto block_11;
}
}
else
{
goto block_9;
}
}
block_23:
{
uint32_t x_19; uint8_t x_20; 
x_19 = 97;
x_20 = lean_uint32_dec_le(x_19, x_18);
if (x_20 == 0)
{
x_12 = x_18;
x_13 = x_20;
goto block_17;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 122;
x_22 = lean_uint32_dec_le(x_18, x_21);
x_12 = x_18;
x_13 = x_22;
goto block_17;
}
}
block_31:
{
if (x_24 == 0)
{
lean_object* x_25; uint32_t x_26; uint32_t x_27; uint8_t x_28; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_string_utf8_get(x_1, x_25);
x_27 = 65;
x_28 = lean_uint32_dec_le(x_27, x_26);
if (x_28 == 0)
{
x_18 = x_26;
goto block_23;
}
else
{
uint32_t x_29; uint8_t x_30; 
x_29 = 90;
x_30 = lean_uint32_dec_le(x_26, x_29);
if (x_30 == 0)
{
x_18 = x_26;
goto block_23;
}
else
{
goto block_9;
}
}
}
else
{
lean_dec_ref(x_1);
return x_24;
}
}
block_34:
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(x_1, x_32);
x_24 = x_33;
goto block_31;
}
block_40:
{
if (x_37 == 0)
{
uint8_t x_38; uint8_t x_39; 
x_38 = l_Lean_isIdFirstAscii___closed__0;
x_39 = lean_uint8_dec_eq(x_36, x_38);
if (x_39 == 0)
{
x_24 = x_39;
goto block_31;
}
else
{
goto block_34;
}
}
else
{
goto block_34;
}
}
block_46:
{
if (x_41 == 0)
{
uint8_t x_42; uint8_t x_43; 
x_42 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_43 = lean_uint8_dec_le(x_42, x_36);
if (x_43 == 0)
{
x_37 = x_43;
goto block_40;
}
else
{
uint8_t x_44; uint8_t x_45; 
x_44 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_45 = lean_uint8_dec_le(x_36, x_44);
x_37 = x_45;
goto block_40;
}
}
else
{
goto block_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_11; uint32_t x_13; uint8_t x_14; uint32_t x_19; uint8_t x_25; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_42; uint8_t x_48; uint8_t x_49; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_string_get_byte_fast(x_1, x_36);
x_48 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_49 = lean_uint8_dec_le(x_48, x_37);
if (x_49 == 0)
{
x_42 = x_49;
goto block_47;
}
else
{
uint8_t x_50; uint8_t x_51; 
x_50 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_51 = lean_uint8_dec_le(x_37, x_50);
x_42 = x_51;
goto block_47;
}
block_10:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_substring_drop(x_5, x_6);
x_8 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0;
x_9 = lean_substring_all(x_7, x_8);
return x_9;
}
block_12:
{
if (x_11 == 0)
{
lean_dec_ref(x_1);
return x_11;
}
else
{
goto block_10;
}
}
block_18:
{
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 95;
x_16 = lean_uint32_dec_eq(x_13, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_isLetterLike(x_13);
x_11 = x_17;
goto block_12;
}
else
{
x_11 = x_16;
goto block_12;
}
}
else
{
goto block_10;
}
}
block_24:
{
uint32_t x_20; uint8_t x_21; 
x_20 = 97;
x_21 = lean_uint32_dec_le(x_20, x_19);
if (x_21 == 0)
{
x_13 = x_19;
x_14 = x_21;
goto block_18;
}
else
{
uint32_t x_22; uint8_t x_23; 
x_22 = 122;
x_23 = lean_uint32_dec_le(x_19, x_22);
x_13 = x_19;
x_14 = x_23;
goto block_18;
}
}
block_32:
{
if (x_25 == 0)
{
lean_object* x_26; uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_string_utf8_get(x_1, x_26);
x_28 = 65;
x_29 = lean_uint32_dec_le(x_28, x_27);
if (x_29 == 0)
{
x_19 = x_27;
goto block_24;
}
else
{
uint32_t x_30; uint8_t x_31; 
x_30 = 90;
x_31 = lean_uint32_dec_le(x_27, x_30);
if (x_31 == 0)
{
x_19 = x_27;
goto block_24;
}
else
{
goto block_10;
}
}
}
else
{
lean_dec_ref(x_1);
return x_25;
}
}
block_35:
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(x_1, x_33);
x_25 = x_34;
goto block_32;
}
block_41:
{
if (x_38 == 0)
{
uint8_t x_39; uint8_t x_40; 
x_39 = l_Lean_isIdFirstAscii___closed__0;
x_40 = lean_uint8_dec_eq(x_37, x_39);
if (x_40 == 0)
{
x_25 = x_40;
goto block_32;
}
else
{
goto block_35;
}
}
else
{
goto block_35;
}
}
block_47:
{
if (x_42 == 0)
{
uint8_t x_43; uint8_t x_44; 
x_43 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_44 = lean_uint8_dec_le(x_43, x_37);
if (x_44 == 0)
{
x_38 = x_44;
goto block_41;
}
else
{
uint8_t x_45; uint8_t x_46; 
x_45 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_46 = lean_uint8_dec_le(x_37, x_45);
x_38 = x_46;
goto block_41;
}
}
else
{
goto block_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 171;
x_2 = l_Lean_versionString___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 187;
x_2 = l_Lean_versionString___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
x_3 = lean_string_append(x_2, x_1);
x_4 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_escape___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Meta_Defs_0__Lean_Name_escape(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_isIdEndEscape___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_21; uint32_t x_23; uint8_t x_24; uint32_t x_29; uint8_t x_35; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_string_utf8_byte_size(x_1);
x_49 = lean_nat_dec_lt(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
x_51 = lean_string_append(x_50, x_1);
lean_dec_ref(x_1);
x_52 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
if (x_2 == 0)
{
uint8_t x_55; uint8_t x_56; uint8_t x_60; uint8_t x_66; uint8_t x_67; 
x_55 = lean_string_get_byte_fast(x_1, x_47);
x_66 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_67 = lean_uint8_dec_le(x_66, x_55);
if (x_67 == 0)
{
x_60 = x_67;
goto block_65;
}
else
{
uint8_t x_68; uint8_t x_69; 
x_68 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_69 = lean_uint8_dec_le(x_55, x_68);
x_60 = x_69;
goto block_65;
}
block_59:
{
if (x_56 == 0)
{
uint8_t x_57; uint8_t x_58; 
x_57 = l_Lean_isIdFirstAscii___closed__0;
x_58 = lean_uint8_dec_eq(x_55, x_57);
if (x_58 == 0)
{
x_35 = x_58;
goto block_43;
}
else
{
goto block_46;
}
}
else
{
goto block_46;
}
}
block_65:
{
if (x_60 == 0)
{
uint8_t x_61; uint8_t x_62; 
x_61 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_62 = lean_uint8_dec_le(x_61, x_55);
if (x_62 == 0)
{
x_56 = x_62;
goto block_59;
}
else
{
uint8_t x_63; uint8_t x_64; 
x_63 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_64 = lean_uint8_dec_le(x_55, x_63);
x_56 = x_64;
goto block_59;
}
}
else
{
goto block_46;
}
}
}
else
{
goto block_11;
}
}
block_11:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0;
lean_inc_ref(x_1);
x_4 = lean_string_any(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
x_6 = lean_string_append(x_5, x_1);
lean_dec_ref(x_1);
x_7 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_1);
x_10 = lean_box(0);
return x_10;
}
}
block_20:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_substring_drop(x_14, x_15);
x_17 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0;
x_18 = lean_substring_all(x_16, x_17);
if (x_18 == 0)
{
goto block_11;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
}
block_22:
{
if (x_21 == 0)
{
goto block_11;
}
else
{
goto block_20;
}
}
block_28:
{
if (x_24 == 0)
{
uint32_t x_25; uint8_t x_26; 
x_25 = 95;
x_26 = lean_uint32_dec_eq(x_23, x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_isLetterLike(x_23);
x_21 = x_27;
goto block_22;
}
else
{
x_21 = x_26;
goto block_22;
}
}
else
{
goto block_20;
}
}
block_34:
{
uint32_t x_30; uint8_t x_31; 
x_30 = 97;
x_31 = lean_uint32_dec_le(x_30, x_29);
if (x_31 == 0)
{
x_23 = x_29;
x_24 = x_31;
goto block_28;
}
else
{
uint32_t x_32; uint8_t x_33; 
x_32 = 122;
x_33 = lean_uint32_dec_le(x_29, x_32);
x_23 = x_29;
x_24 = x_33;
goto block_28;
}
}
block_43:
{
if (x_35 == 0)
{
lean_object* x_36; uint32_t x_37; uint32_t x_38; uint8_t x_39; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_string_utf8_get(x_1, x_36);
x_38 = 65;
x_39 = lean_uint32_dec_le(x_38, x_37);
if (x_39 == 0)
{
x_29 = x_37;
goto block_34;
}
else
{
uint32_t x_40; uint8_t x_41; 
x_40 = 90;
x_41 = lean_uint32_dec_le(x_37, x_40);
if (x_41 == 0)
{
x_29 = x_37;
goto block_34;
}
else
{
goto block_20;
}
}
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_1);
return x_42;
}
}
block_46:
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(x_1, x_44);
x_35 = x_45;
goto block_43;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 187;
x_3 = lean_uint32_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_14; uint32_t x_25; uint8_t x_26; 
x_25 = 65;
x_26 = lean_uint32_dec_le(x_25, x_1);
if (x_26 == 0)
{
goto block_24;
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = 90;
x_28 = lean_uint32_dec_le(x_1, x_27);
if (x_28 == 0)
{
goto block_24;
}
else
{
return x_28;
}
}
block_13:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 95;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 39;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 33;
x_8 = lean_uint32_dec_eq(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 63;
x_10 = lean_uint32_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_isLetterLike(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isSubScriptAlnum(x_1);
return x_12;
}
else
{
return x_11;
}
}
else
{
return x_10;
}
}
else
{
return x_8;
}
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_19:
{
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 48;
x_16 = lean_uint32_dec_le(x_15, x_1);
if (x_16 == 0)
{
x_2 = x_16;
goto block_13;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 57;
x_18 = lean_uint32_dec_le(x_1, x_17);
x_2 = x_18;
goto block_13;
}
}
else
{
return x_14;
}
}
block_24:
{
uint32_t x_20; uint8_t x_21; 
x_20 = 97;
x_21 = lean_uint32_dec_le(x_20, x_1);
if (x_21 == 0)
{
x_14 = x_21;
goto block_19;
}
else
{
uint32_t x_22; uint8_t x_23; 
x_22 = 122;
x_23 = lean_uint32_dec_le(x_1, x_22);
x_14 = x_23;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___lam__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(uint8_t x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
x_8 = lean_string_append(x_7, x_2);
lean_dec_ref(x_2);
x_9 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0;
if (x_3 == 0)
{
lean_object* x_18; uint8_t x_24; uint32_t x_26; uint8_t x_27; uint32_t x_32; uint8_t x_38; uint8_t x_48; uint8_t x_49; uint8_t x_53; uint8_t x_59; uint8_t x_60; 
x_18 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1;
x_48 = lean_string_get_byte_fast(x_2, x_4);
x_59 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_60 = lean_uint8_dec_le(x_59, x_48);
if (x_60 == 0)
{
x_53 = x_60;
goto block_58;
}
else
{
uint8_t x_61; uint8_t x_62; 
x_61 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_62 = lean_uint8_dec_le(x_48, x_61);
x_53 = x_62;
goto block_58;
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc_ref(x_2);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_4);
lean_ctor_set(x_19, 2, x_5);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_substring_drop(x_19, x_20);
x_22 = lean_substring_all(x_21, x_18);
if (x_22 == 0)
{
goto block_17;
}
else
{
return x_2;
}
}
block_25:
{
if (x_24 == 0)
{
goto block_17;
}
else
{
goto block_23;
}
}
block_31:
{
if (x_27 == 0)
{
uint32_t x_28; uint8_t x_29; 
x_28 = 95;
x_29 = lean_uint32_dec_eq(x_26, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_isLetterLike(x_26);
x_24 = x_30;
goto block_25;
}
else
{
x_24 = x_29;
goto block_25;
}
}
else
{
goto block_23;
}
}
block_37:
{
uint32_t x_33; uint8_t x_34; 
x_33 = 97;
x_34 = lean_uint32_dec_le(x_33, x_32);
if (x_34 == 0)
{
x_26 = x_32;
x_27 = x_34;
goto block_31;
}
else
{
uint32_t x_35; uint8_t x_36; 
x_35 = 122;
x_36 = lean_uint32_dec_le(x_32, x_35);
x_26 = x_32;
x_27 = x_36;
goto block_31;
}
}
block_44:
{
if (x_38 == 0)
{
uint32_t x_39; uint32_t x_40; uint8_t x_41; 
x_39 = lean_string_utf8_get(x_2, x_4);
x_40 = 65;
x_41 = lean_uint32_dec_le(x_40, x_39);
if (x_41 == 0)
{
x_32 = x_39;
goto block_37;
}
else
{
uint32_t x_42; uint8_t x_43; 
x_42 = 90;
x_43 = lean_uint32_dec_le(x_39, x_42);
if (x_43 == 0)
{
x_32 = x_39;
goto block_37;
}
else
{
goto block_23;
}
}
}
else
{
return x_2;
}
}
block_47:
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(x_2, x_45);
x_38 = x_46;
goto block_44;
}
block_52:
{
if (x_49 == 0)
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_Lean_isIdFirstAscii___closed__0;
x_51 = lean_uint8_dec_eq(x_48, x_50);
if (x_51 == 0)
{
x_38 = x_51;
goto block_44;
}
else
{
goto block_47;
}
}
else
{
goto block_47;
}
}
block_58:
{
if (x_53 == 0)
{
uint8_t x_54; uint8_t x_55; 
x_54 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_55 = lean_uint8_dec_le(x_54, x_48);
if (x_55 == 0)
{
x_49 = x_55;
goto block_52;
}
else
{
uint8_t x_56; uint8_t x_57; 
x_56 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_57 = lean_uint8_dec_le(x_48, x_56);
x_49 = x_57;
goto block_52;
}
}
else
{
goto block_47;
}
}
}
else
{
goto block_17;
}
block_17:
{
uint8_t x_12; 
lean_inc_ref(x_2);
x_12 = lean_string_any(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
x_14 = lean_string_append(x_13, x_2);
lean_dec_ref(x_2);
x_15 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
x_16 = lean_string_append(x_14, x_15);
return x_16;
}
else
{
return x_2;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_3);
x_6 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[anonymous]", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_5; 
lean_dec_ref(x_4);
x_5 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0;
return x_5;
}
case 1:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
lean_inc_ref(x_7);
x_8 = lean_apply_1(x_4, x_7);
x_9 = lean_unbox(x_8);
x_10 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(x_2, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_6);
x_11 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_3);
lean_inc_ref(x_4);
x_12 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(x_1, x_2, x_6, x_4);
x_13 = lean_string_append(x_12, x_1);
x_14 = 0;
lean_inc_ref(x_11);
x_15 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(x_2, x_11, x_14);
lean_inc_ref(x_13);
x_16 = lean_string_append(x_13, x_15);
lean_dec_ref(x_15);
if (x_2 == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_4);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_16);
x_17 = lean_apply_1(x_4, x_16);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_13);
lean_dec_ref(x_11);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_16);
x_19 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(x_2, x_11, x_2);
x_20 = lean_string_append(x_13, x_19);
lean_dec_ref(x_19);
return x_20;
}
}
}
}
default: 
{
lean_object* x_21; 
lean_dec_ref(x_4);
x_21 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec_ref(x_3);
x_23 = l_Nat_reprFast(x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_21);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_dec_ref(x_3);
x_25 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1;
x_26 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(x_1, x_2, x_21, x_25);
x_27 = lean_string_append(x_26, x_1);
x_28 = l_Nat_reprFast(x_24);
x_29 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(x_1, x_5, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\?", 1, 1);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1;
x_3 = lean_name_eq(x_1, x_2);
x_4 = 1;
if (x_3 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Name_getRoot(x_1);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2;
lean_inc_ref(x_6);
x_8 = lean_string_isprefixof(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3;
x_10 = lean_string_isprefixof(x_9, x_6);
return x_10;
}
else
{
lean_dec_ref(x_6);
return x_4;
}
}
else
{
lean_dec(x_5);
return x_3;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_versionStringCore___closed__1;
if (x_2 == 0)
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(x_4, x_2, x_1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
lean_inc(x_1);
x_6 = lean_is_inaccessible_user_name(x_1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Name_hasMacroScopes(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(x_4, x_2, x_1, x_3);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(x_4, x_7, x_1, x_3);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(x_4, x_6, x_1, x_3);
return x_11;
}
}
else
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep(x_4, x_12, x_1, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0;
return x_4;
}
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_3);
x_7 = 0;
x_8 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(x_2, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_5);
x_9 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_3);
x_10 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(x_1, x_2, x_5);
x_11 = lean_string_append(x_10, x_1);
x_12 = 0;
x_13 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape(x_2, x_9, x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec_ref(x_13);
return x_14;
}
}
default: 
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec_ref(x_3);
x_17 = l_Nat_reprFast(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_15);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec_ref(x_3);
x_19 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(x_1, x_2, x_15);
x_20 = lean_string_append(x_19, x_1);
x_21 = l_Nat_reprFast(x_18);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(x_1, x_4, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_versionStringCore___closed__1;
if (x_2 == 0)
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(x_3, x_2, x_1);
return x_4;
}
else
{
uint8_t x_5; 
lean_inc(x_1);
x_5 = lean_is_inaccessible_user_name(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Name_hasMacroScopes(x_1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(x_3, x_2, x_1);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(x_3, x_6, x_1);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(x_3, x_5, x_1);
return x_10;
}
}
else
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0_spec__0(x_3, x_11, x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Name_hasNum(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
x_1 = x_3;
goto _start;
}
default: 
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_hasNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Name_reprPrec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Name.anonymous", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Name_reprPrec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_reprPrec___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Name_reprPrec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Name_reprPrec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_reprPrec___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Name_reprPrec___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Name.mkStr ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Name_reprPrec___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_reprPrec___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Name_reprPrec___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Name_reprPrec___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_reprPrec___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Name_reprPrec___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Name.mkNum ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Name_reprPrec___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_reprPrec___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_Name_reprPrec___closed__1;
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Init_Meta_Defs_0__Lean_Name_hasNum(x_4);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = 1;
x_8 = l_Lean_Name_reprPrec___closed__3;
x_9 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(x_1, x_7);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
lean_dec_ref(x_1);
x_12 = l_Lean_Name_reprPrec___closed__5;
x_13 = lean_unsigned_to_nat(1024u);
x_14 = l_Lean_Name_reprPrec(x_4, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Name_reprPrec___closed__7;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_String_quote(x_5);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Repr_addAppParen(x_20, x_2);
return x_21;
}
}
default: 
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec_ref(x_1);
x_24 = l_Lean_Name_reprPrec___closed__9;
x_25 = lean_unsigned_to_nat(1024u);
x_26 = l_Lean_Name_reprPrec(x_22, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Name_reprPrec___closed__7;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Nat_reprFast(x_23);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Repr_addAppParen(x_32, x_2);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_reprPrec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_reprPrec(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Name_instRepr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_reprPrec___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Name_instRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_instRepr___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_capitalize(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_string_capitalize(x_3);
x_5 = l_Lean_Name_str___override(x_2, x_4);
return x_5;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
return x_1;
}
}
case 1:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
x_6 = lean_name_eq(x_1, x_2);
lean_dec_ref(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Name_replacePrefix(x_4, x_2, x_3);
x_8 = l_Lean_Name_str___override(x_7, x_5);
return x_8;
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_inc(x_3);
return x_3;
}
}
default: 
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_name_eq(x_1, x_2);
lean_dec_ref(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Name_replacePrefix(x_9, x_2, x_3);
x_13 = l_Lean_Name_num___override(x_12, x_10);
return x_13;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_inc(x_3);
return x_3;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_replacePrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Name_replacePrefix(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
case 1:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_string_dec_eq(x_7, x_5);
lean_dec_ref(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_box(0);
return x_9;
}
else
{
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
}
default: 
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_nat_dec_eq(x_15, x_13);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_box(0);
return x_17;
}
else
{
x_1 = x_14;
x_2 = x_12;
goto _start;
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_eraseSuffix_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_eraseSuffix_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_modifyBase(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_hasMacroScopes(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_1);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_extractMacroScopes(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_apply_1(x_2, x_7);
lean_ctor_set(x_5, 0, x_8);
x_9 = l_Lean_MacroScopesView_review(x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_14 = lean_apply_1(x_2, x_10);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
x_16 = l_Lean_MacroScopesView_review(x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendAfter___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_string_append(x_4, x_1);
lean_dec_ref(x_1);
x_6 = l_Lean_Name_str___override(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Lean_Name_str___override(x_2, x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_after(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_hasMacroScopes(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Name_appendAfter___lam__0(x_2, x_1);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_extractMacroScopes(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Name_appendAfter___lam__0(x_2, x_7);
lean_ctor_set(x_5, 0, x_8);
x_9 = l_Lean_MacroScopesView_review(x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_14 = l_Lean_Name_appendAfter___lam__0(x_2, x_10);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
x_16 = l_Lean_MacroScopesView_review(x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendIndexAfter___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Nat_reprFast(x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = l_Lean_Name_str___override(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0;
x_11 = l_Nat_reprFast(x_1);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = l_Lean_Name_str___override(x_2, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* lean_name_append_index_after(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_hasMacroScopes(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Name_appendIndexAfter___lam__0(x_2, x_1);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_extractMacroScopes(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Name_appendIndexAfter___lam__0(x_2, x_7);
lean_ctor_set(x_5, 0, x_8);
x_9 = l_Lean_MacroScopesView_review(x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_14 = l_Lean_Name_appendIndexAfter___lam__0(x_2, x_10);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
x_16 = l_Lean_MacroScopesView_review(x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Name_appendBefore___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_string_append(x_1, x_5);
lean_dec_ref(x_5);
x_7 = l_Lean_Name_str___override(x_4, x_6);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l_Lean_Name_str___override(x_8, x_1);
x_11 = l_Lean_Name_num___override(x_10, x_9);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* lean_name_append_before(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_hasMacroScopes(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Name_appendBefore___lam__0(x_2, x_1);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_extractMacroScopes(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Name_appendBefore___lam__0(x_2, x_7);
lean_ctor_set(x_5, 0, x_8);
x_9 = l_Lean_MacroScopesView_review(x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_14 = l_Lean_Name_appendBefore___lam__0(x_2, x_10);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
x_16 = l_Lean_MacroScopesView_review(x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_5(x_6, x_1, x_2, lean_box(0), lean_box(0), lean_box(0));
return x_9;
}
}
case 1:
{
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
x_14 = lean_apply_4(x_4, x_10, x_11, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_apply_5(x_6, x_1, x_2, lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
}
default: 
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec_ref(x_2);
x_20 = lean_apply_4(x_5, x_16, x_17, x_18, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_5);
x_21 = lean_apply_5(x_6, x_1, x_2, lean_box(0), lean_box(0), lean_box(0));
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Name_beq_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_4, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_5(x_7, x_2, x_3, lean_box(0), lean_box(0), lean_box(0));
return x_10;
}
}
case 1:
{
lean_dec(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_3);
x_15 = lean_apply_4(x_5, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_apply_5(x_7, x_2, x_3, lean_box(0), lean_box(0), lean_box(0));
return x_16;
}
}
default: 
{
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_dec_ref(x_3);
x_21 = lean_apply_4(x_6, x_17, x_18, x_19, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_6);
x_22 = lean_apply_5(x_7, x_2, x_3, lean_box(0), lean_box(0), lean_box(0));
return x_22;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Name_instDecidableEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Name_instDecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Name_instDecidableEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_curr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Name_num___override(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_next(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameGenerator_mkChild(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Name_num___override(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
x_12 = l_Lean_Name_num___override(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_nat_add(x_11, x_13);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
x_8 = l_Lean_Name_num___override(x_6, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_7, x_10);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_11);
x_12 = lean_apply_1(x_2, x_4);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_15);
lean_inc(x_14);
x_16 = l_Lean_Name_num___override(x_14, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__0), 3, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_15, x_18);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_apply_1(x_2, x_20);
x_22 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_21, x_17);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec_ref(x_3);
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_mkFreshId___redArg___lam__1), 4, 3);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_4);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkFreshId___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_2(x_1, lean_box(0), x_4);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_apply_2(x_1, lean_box(0), x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_monadNameGeneratorLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_monadNameGeneratorLift___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = l_String_quote(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_2 = x_9;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = l_String_quote(x_11);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = l_String_quote(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(x_1, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = l_String_quote(x_11);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1_spec__3(x_1, x_16, x_12);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_quote(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0___lam__0(x_7);
x_9 = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0_spec__1(x_2, x_8, x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5;
x_4 = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__0(x_1, x_3);
x_5 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8;
x_6 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9;
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Std_Format_fill(x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Syntax.Preresolved.namespace", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instReprPreresolved_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Syntax_instReprPreresolved_repr___closed__1;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Syntax.Preresolved.decl", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instReprPreresolved_repr___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Syntax_instReprPreresolved_repr___closed__6;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_nat_dec_le(x_14, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_4 = x_16;
goto block_13;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_4 = x_17;
goto block_13;
}
block_13:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_Syntax_instReprPreresolved_repr___closed__2;
x_6 = lean_unsigned_to_nat(1024u);
x_7 = l_Lean_Name_reprPrec(x_3, x_6);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = 0;
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_35; uint8_t x_36; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_20 = x_1;
} else {
 lean_dec_ref(x_1);
 x_20 = lean_box(0);
}
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_21 = x_37;
goto block_34;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_21 = x_38;
goto block_34;
}
block_34:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_box(1);
x_23 = l_Lean_Syntax_instReprPreresolved_repr___closed__7;
x_24 = lean_unsigned_to_nat(1024u);
x_25 = l_Lean_Name_reprPrec(x_18, x_24);
if (lean_is_scalar(x_20)) {
 x_26 = lean_alloc_ctor(5, 2, 0);
} else {
 x_26 = x_20;
 lean_ctor_set_tag(x_26, 5);
}
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
x_28 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(x_19);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
x_31 = 0;
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = l_Repr_addAppParen(x_32, x_2);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprPreresolved_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_instReprPreresolved_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_instReprPreresolved_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instReprPreresolved() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_instReprPreresolved___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_instReprPreresolved_repr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_instReprPreresolved_repr(x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_2 = x_9;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_instReprPreresolved_repr(x_11, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_instReprPreresolved_repr(x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(x_1, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_instReprPreresolved_repr(x_11, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4_spec__6(x_1, x_16, x_12);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2___lam__0(x_7);
x_9 = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2_spec__4(x_2, x_8, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_3 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5;
x_4 = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Syntax_instRepr_repr_spec__1_spec__2(x_1, x_3);
x_5 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8;
x_6 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9;
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Syntax.missing", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instRepr_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Syntax.node", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instRepr_repr___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Syntax_instRepr_repr___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_instRepr_repr(x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_2 = x_9;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_instRepr_repr(x_11, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_instRepr_repr(x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(x_1, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_instRepr_repr(x_11, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1_spec__3(x_1, x_16, x_12);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(x_7);
x_9 = l_List_foldl___at___00Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0_spec__1(x_2, x_8, x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[]", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_array_to_list(x_1);
x_6 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5;
x_7 = l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0(x_5, x_6);
x_8 = l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2;
x_9 = l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Std_Format_fill(x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5;
return x_15;
}
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Syntax.atom", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instRepr_repr___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Syntax_instRepr_repr___closed__6;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Syntax.ident", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instRepr_repr___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Syntax_instRepr_repr___closed__9;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr_repr___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".toRawSubstring", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1024u);
x_11 = lean_nat_dec_le(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_3 = x_12;
goto block_9;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_3 = x_13;
goto block_9;
}
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_34; uint8_t x_35; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_34 = lean_unsigned_to_nat(1024u);
x_35 = lean_nat_dec_le(x_34, x_2);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_17 = x_36;
goto block_33;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_17 = x_37;
goto block_33;
}
block_33:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_box(1);
x_19 = l_Lean_Syntax_instRepr_repr___closed__4;
x_20 = lean_unsigned_to_nat(1024u);
x_21 = l_instReprSourceInfo_repr(x_14, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = l_Lean_Name_reprPrec(x_15, x_20);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
x_27 = l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0(x_16);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
x_30 = 0;
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = l_Repr_addAppParen(x_31, x_2);
return x_32;
}
}
case 2:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_56; uint8_t x_57; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_39);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_40 = x_1;
} else {
 lean_dec_ref(x_1);
 x_40 = lean_box(0);
}
x_56 = lean_unsigned_to_nat(1024u);
x_57 = lean_nat_dec_le(x_56, x_2);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_41 = x_58;
goto block_55;
}
else
{
lean_object* x_59; 
x_59 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_41 = x_59;
goto block_55;
}
block_55:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_box(1);
x_43 = l_Lean_Syntax_instRepr_repr___closed__7;
x_44 = lean_unsigned_to_nat(1024u);
x_45 = l_instReprSourceInfo_repr(x_38, x_44);
if (lean_is_scalar(x_40)) {
 x_46 = lean_alloc_ctor(5, 2, 0);
} else {
 x_46 = x_40;
 lean_ctor_set_tag(x_46, 5);
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
x_48 = l_String_quote(x_39);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_50);
x_52 = 0;
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = l_Repr_addAppParen(x_53, x_2);
return x_54;
}
}
default: 
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_88; uint8_t x_89; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_1, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 3);
lean_inc(x_63);
lean_dec_ref(x_1);
x_88 = lean_unsigned_to_nat(1024u);
x_89 = lean_nat_dec_le(x_88, x_2);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_64 = x_90;
goto block_87;
}
else
{
lean_object* x_91; 
x_91 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_64 = x_91;
goto block_87;
}
block_87:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_65 = lean_box(1);
x_66 = l_Lean_Syntax_instRepr_repr___closed__10;
x_67 = lean_unsigned_to_nat(1024u);
x_68 = l_instReprSourceInfo_repr(x_60, x_67);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
x_71 = lean_substring_tostring(x_61);
x_72 = l_String_quote(x_71);
x_73 = l_Lean_Syntax_instRepr_repr___closed__11;
x_74 = lean_string_append(x_72, x_73);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_65);
x_78 = l_Lean_Name_reprPrec(x_62, x_67);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_65);
x_81 = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(x_63);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_83, 0, x_64);
lean_ctor_set(x_83, 1, x_82);
x_84 = 0;
x_85 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = l_Repr_addAppParen(x_85, x_2);
return x_86;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Syntax_instRepr_repr___closed__1;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_instRepr_repr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instRepr_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_instRepr_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___00Lean_Syntax_instRepr_repr_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_instRepr_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_instRepr___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("raw", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5;
x_2 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6;
x_3 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_instRepr_repr(x_1, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = 0;
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10;
x_11 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_instReprTSyntax_repr___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_instReprTSyntax_repr(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprTSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_instReprTSyntax_repr___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeConsSyntaxNodeKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TSyntax_instCoeConsSyntaxNodeKind(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_instCoeIdentTerm___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeIdentTerm___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TSyntax_instCoeIdentTerm___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeIdentTerm() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TSyntax_instCoeIdentTerm___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_instCoeDepTermMkIdentIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeStrLitTerm() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TSyntax_instCoeIdentTerm___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeNameLitTerm() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TSyntax_instCoeIdentTerm___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeScientificLitTerm() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TSyntax_instCoeIdentTerm___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeNumLitTerm() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TSyntax_instCoeIdentTerm___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeCharLitTerm() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TSyntax_instCoeIdentTerm___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeIdentLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TSyntax_instCoeIdentTerm___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeNumLitPrio() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TSyntax_instCoeIdentTerm___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_instCoeNumLitPrec() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TSyntax_instCoeIdentTerm___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_instCoeIdentTerm___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_Compat_instCoeTailSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSyntaxArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TSyntaxArray_mkImpl___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_string_dec_eq(x_6, x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_name_eq(x_7, x_9);
if (x_11 == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_List_beq___at___00Lean_Syntax_instBEqPreresolved_beq_spec__0(x_8, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqPreresolved_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_instBEqPreresolved_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_instBEqPreresolved___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_instBEqPreresolved_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instBEqPreresolved() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_instBEqPreresolved___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structEq_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Syntax_instBEqPreresolved_beq(x_6, x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structEq_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___00Lean_Syntax_structEq_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structEq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = lean_name_eq(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
if (x_9 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_array_get_size(x_8);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_6);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(x_6, x_8, x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
return x_13;
}
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = 0;
return x_14;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_2);
x_17 = lean_string_dec_eq(x_15, x_16);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = 0;
return x_18;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_28; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_dec_ref(x_2);
x_28 = lean_substring_beq(x_19, x_22);
if (x_28 == 0)
{
lean_dec(x_23);
lean_dec(x_20);
x_25 = x_28;
goto block_27;
}
else
{
uint8_t x_29; 
x_29 = lean_name_eq(x_20, x_23);
lean_dec(x_23);
lean_dec(x_20);
x_25 = x_29;
goto block_27;
}
block_27:
{
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_21);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l_List_beq___at___00Lean_Syntax_structEq_spec__1(x_21, x_24);
lean_dec(x_24);
lean_dec(x_21);
return x_26;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_30 = 0;
return x_30;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = lean_array_fget_borrowed(x_2, x_7);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Syntax_structEq(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_structEq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___00Lean_Syntax_structEq_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Syntax_instBEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_structEq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instBEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_instBEq___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_instBEq___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqTSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_instBEqTSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_array_fget_borrowed(x_1, x_7);
x_9 = l_Lean_Syntax_getTailInfo_x3f(x_8);
if (lean_obj_tag(x_9) == 0)
{
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_7);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 3:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_array_get_size(x_7);
x_9 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
}
default: 
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_Syntax_getTailInfo_x3f_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTailInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo_x3f(x_1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_nat_sub(x_6, x_5);
lean_dec(x_5);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(0u);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTrailingSize(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
x_3 = l_Lean_SourceInfo_getTrailing_x3f(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailing_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTrailing_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_getTailInfo(x_1);
x_4 = l_Lean_SourceInfo_getTrailingTailPos_x3f(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getTrailingTailPos_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Syntax_getTrailingTailPos_x3f(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object* x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getHeadInfo(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; 
x_8 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_12 = x_5;
} else {
 lean_dec_ref(x_5);
 x_12 = lean_box(0);
}
if (x_2 == 0)
{
lean_dec(x_11);
x_18 = x_6;
goto block_20;
}
else
{
lean_dec(x_6);
x_18 = x_11;
goto block_20;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
if (lean_is_scalar(x_12)) {
 x_15 = lean_alloc_ctor(0, 3, 0);
} else {
 x_15 = x_12;
}
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_20:
{
if (x_3 == 0)
{
lean_dec_ref(x_8);
x_13 = x_18;
x_14 = x_9;
goto block_17;
}
else
{
lean_object* x_19; 
lean_dec(x_9);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
lean_dec_ref(x_8);
x_13 = x_18;
x_14 = x_19;
goto block_17;
}
}
}
else
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_21 = lean_box(0);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = lean_box(0);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSubstring_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
x_5 = lean_unbox(x_3);
x_6 = l_Lean_Syntax_getSubstring_x3f(x_1, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget_borrowed(x_1, x_8);
lean_inc_ref(x_2);
lean_inc(x_9);
x_10 = lean_apply_1(x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_array_fset(x_1, x_8, x_13);
lean_dec(x_8);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_array_fset(x_1, x_8, x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfoAux(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 3:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
case 1:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_array_get_size(x_20);
x_22 = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(x_1, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_18);
x_23 = lean_box(0);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_2, 2, x_25);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_ctor_set(x_2, 2, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_31 = lean_array_get_size(x_30);
x_32 = l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(x_1, x_30, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_box(0);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_34);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
default: 
{
lean_object* x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateLast___at___00Lean_Syntax_setTailInfoAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget_borrowed(x_2, x_8);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_Syntax_setTailInfoAux(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_array_fset(x_2, x_8, x_13);
lean_dec(x_8);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_array_fset(x_2, x_8, x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setTailInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_setTailInfoAux(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unsetTrailing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
lean_dec(x_7);
lean_inc(x_6);
lean_ctor_set(x_4, 2, x_6);
x_8 = l_Lean_Syntax_setTailInfo(x_1, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_2, 2, x_11);
x_12 = l_Lean_Syntax_setTailInfo(x_1, x_2);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_inc(x_13);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_17 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 x_19 = x_13;
} else {
 lean_dec_ref(x_13);
 x_19 = lean_box(0);
}
lean_inc(x_18);
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(0, 3, 0);
} else {
 x_20 = x_19;
}
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_18);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_16);
x_22 = l_Lean_Syntax_setTailInfo(x_1, x_21);
return x_22;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget_borrowed(x_1, x_3);
lean_inc_ref(x_2);
lean_inc(x_7);
x_8 = lean_apply_1(x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_array_fset(x_1, x_3, x_13);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_fset(x_1, x_3, x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfoAux(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 3:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
case 1:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___redArg(x_1, x_20, x_21);
if (lean_obj_tag(x_22) == 1)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_2, 2, x_24);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_2, 2, x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_2);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_22);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_18);
x_27 = lean_box(0);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___redArg(x_1, x_30, x_31);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_33);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
x_37 = lean_box(0);
return x_37;
}
}
}
default: 
{
lean_object* x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget_borrowed(x_2, x_3);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lean_Syntax_setHeadInfoAux(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_array_fset(x_2, x_3, x_13);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_array_fset(x_2, x_3, x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_Defs_0__Lean_Syntax_updateFirst___at___00Lean_Syntax_setHeadInfoAux_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setHeadInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_setHeadInfoAux(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec(x_1);
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
case 2:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
default: 
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_17 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_16);
return x_17;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_getHead_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getHead_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
x_4 = l_Lean_SourceInfo_getPos_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
}
}
case 3:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = 0;
x_11 = l_Lean_SourceInfo_getPos_x3f(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = l_Lean_Syntax_getHead_x3f___closed__0;
x_21 = lean_array_size(x_17);
x_22 = 0;
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(x_19, x_20, x_17, x_21, x_22, x_20);
lean_dec_ref(x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
if (lean_obj_tag(x_24) == 0)
{
return x_18;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_1);
return x_26;
}
}
default: 
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_inc_ref(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = l_Lean_Syntax_getHead_x3f(x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
return x_11;
}
else
{
size_t x_12; size_t x_13; 
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
{
size_t _tmp_4 = x_13;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_getHead_x3f_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Syntax_getHeadInfo(x_2);
x_4 = l_Lean_Syntax_setHeadInfo(x_1, x_3);
x_5 = l_Lean_Syntax_getTailInfo(x_2);
x_6 = l_Lean_Syntax_setTailInfo(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_copyHeadTailInfoFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_copyHeadTailInfoFrom(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSynthetic(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 0;
x_3 = l_Lean_SourceInfo_fromRef(x_1, x_2);
x_4 = l_Lean_Syntax_setHeadInfo(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_apply_3(x_2, lean_box(0), x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_withHeadRefOnly___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_getHead_x3f(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_1);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_5);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withHeadRefOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
lean_inc(x_7);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_withHeadRefOnly___redArg___lam__1), 5, 4);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_6);
lean_closure_set(x_9, 3, x_7);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_expandMacros___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_expandMacros___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_expandMacros___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_expandMacros___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("byTactic", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_expandMacros___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_expandMacros___lam__0___closed__3;
x_2 = l_Lean_expandMacros___lam__0___closed__2;
x_3 = l_Lean_expandMacros___lam__0___closed__1;
x_4 = l_Lean_expandMacros___lam__0___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_expandMacros___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_expandMacros___lam__0___closed__4;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
return x_1;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_expandMacros___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_expandMacros___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_expandMacros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_8 = lean_apply_1(x_2, x_6);
x_9 = lean_unbox(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = lean_ctor_get(x_3, 5);
x_18 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set(x_3, 5, x_18);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_19 = l_Lean_Macro_expandMacro_x3f(x_1, x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec_ref(x_3);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_nat_dec_eq(x_15, x_16);
if (x_24 == 0)
{
uint8_t x_25; 
lean_free_object(x_19);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; uint8_t x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_1, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 0);
lean_dec(x_28);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_15, x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_13);
lean_ctor_set(x_31, 2, x_14);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_16);
lean_ctor_set(x_31, 5, x_18);
x_32 = lean_array_size(x_7);
x_33 = 0;
x_34 = lean_unbox(x_8);
x_35 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(x_34, x_32, x_33, x_7, x_31, x_22);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_1, 2, x_37);
lean_ctor_set(x_35, 0, x_1);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_1, 2, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_free_object(x_1);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; uint8_t x_50; lean_object* x_51; 
lean_dec(x_1);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_15, x_45);
lean_dec(x_15);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_13);
lean_ctor_set(x_47, 2, x_14);
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 4, x_16);
lean_ctor_set(x_47, 5, x_18);
x_48 = lean_array_size(x_7);
x_49 = 0;
x_50 = lean_unbox(x_8);
x_51 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(x_50, x_48, x_49, x_7, x_47, x_22);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_5);
lean_ctor_set(x_55, 1, x_6);
lean_ctor_set(x_55, 2, x_52);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_6);
lean_dec(x_5);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_59 = x_51;
} else {
 lean_dec_ref(x_51);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_61 = l_Lean_expandMacros___closed__0;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_62);
return x_19;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_dec(x_19);
x_64 = lean_nat_dec_eq(x_15, x_16);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; uint8_t x_71; lean_object* x_72; 
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_65 = x_1;
} else {
 lean_dec_ref(x_1);
 x_65 = lean_box(0);
}
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_15, x_66);
lean_dec(x_15);
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_12);
lean_ctor_set(x_68, 1, x_13);
lean_ctor_set(x_68, 2, x_14);
lean_ctor_set(x_68, 3, x_67);
lean_ctor_set(x_68, 4, x_16);
lean_ctor_set(x_68, 5, x_18);
x_69 = lean_array_size(x_7);
x_70 = 0;
x_71 = lean_unbox(x_8);
x_72 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(x_71, x_69, x_70, x_7, x_68, x_63);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_76 = lean_alloc_ctor(1, 3, 0);
} else {
 x_76 = x_65;
}
lean_ctor_set(x_76, 0, x_5);
lean_ctor_set(x_76, 1, x_6);
lean_ctor_set(x_76, 2, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_5);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_82 = l_Lean_expandMacros___closed__0;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_63);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_1);
x_85 = lean_ctor_get(x_19, 1);
lean_inc(x_85);
lean_dec_ref(x_19);
x_86 = lean_ctor_get(x_20, 0);
lean_inc(x_86);
lean_dec_ref(x_20);
x_87 = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(x_87, 0, x_8);
x_1 = x_86;
x_2 = x_87;
x_4 = x_85;
goto _start;
}
}
else
{
uint8_t x_89; 
lean_dec_ref(x_3);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_19);
if (x_89 == 0)
{
return x_19;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_19, 0);
x_91 = lean_ctor_get(x_19, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_19);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_93 = lean_ctor_get(x_3, 0);
x_94 = lean_ctor_get(x_3, 1);
x_95 = lean_ctor_get(x_3, 2);
x_96 = lean_ctor_get(x_3, 3);
x_97 = lean_ctor_get(x_3, 4);
x_98 = lean_ctor_get(x_3, 5);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_3);
x_99 = l_Lean_replaceRef(x_1, x_98);
lean_dec(x_98);
lean_inc(x_99);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
x_100 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_100, 0, x_93);
lean_ctor_set(x_100, 1, x_94);
lean_ctor_set(x_100, 2, x_95);
lean_ctor_set(x_100, 3, x_96);
lean_ctor_set(x_100, 4, x_97);
lean_ctor_set(x_100, 5, x_99);
lean_inc_ref(x_100);
lean_inc_ref(x_1);
x_101 = l_Lean_Macro_expandMacro_x3f(x_1, x_100, x_4);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec_ref(x_100);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_nat_dec_eq(x_96, x_97);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; uint8_t x_112; lean_object* x_113; 
lean_dec(x_104);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_106 = x_1;
} else {
 lean_dec_ref(x_1);
 x_106 = lean_box(0);
}
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_add(x_96, x_107);
lean_dec(x_96);
x_109 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_109, 0, x_93);
lean_ctor_set(x_109, 1, x_94);
lean_ctor_set(x_109, 2, x_95);
lean_ctor_set(x_109, 3, x_108);
lean_ctor_set(x_109, 4, x_97);
lean_ctor_set(x_109, 5, x_99);
x_110 = lean_array_size(x_7);
x_111 = 0;
x_112 = lean_unbox(x_8);
x_113 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(x_112, x_110, x_111, x_7, x_109, x_103);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_117 = lean_alloc_ctor(1, 3, 0);
} else {
 x_117 = x_106;
}
lean_ctor_set(x_117, 0, x_5);
lean_ctor_set(x_117, 1, x_6);
lean_ctor_set(x_117, 2, x_114);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_5);
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
x_123 = l_Lean_expandMacros___closed__0;
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_123);
if (lean_is_scalar(x_104)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_104;
 lean_ctor_set_tag(x_125, 1);
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_103);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec_ref(x_1);
x_126 = lean_ctor_get(x_101, 1);
lean_inc(x_126);
lean_dec_ref(x_101);
x_127 = lean_ctor_get(x_102, 0);
lean_inc(x_127);
lean_dec_ref(x_102);
x_128 = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(x_128, 0, x_8);
x_1 = x_127;
x_2 = x_128;
x_3 = x_100;
x_4 = x_126;
goto _start;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec_ref(x_1);
x_130 = lean_ctor_get(x_101, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_101, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_132 = x_101;
} else {
 lean_dec_ref(x_101);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
}
else
{
lean_object* x_134; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_1);
lean_ctor_set(x_134, 1, x_4);
return x_134;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_expandMacros___lam__0___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_array_uget(x_4, x_3);
lean_inc_ref(x_5);
x_12 = l_Lean_expandMacros(x_11, x_10, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_16, x_3, x_13);
x_3 = x_18;
x_4 = x_19;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_expandMacros_spec__0(x_7, x_8, x_9, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_SourceInfo_fromRef(x_1, x_3);
x_5 = 1;
lean_inc(x_2);
x_6 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(x_2, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_byte_size(x_6);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_2);
lean_ctor_set(x_11, 3, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFrom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_mkIdentFrom(x_1, x_2, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_mkIdentFrom(x_4, x_1, x_2);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_mkIdentFromRef___redArg___lam__0(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_box(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_mkIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Lean_mkIdentFromRef___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkIdentFromRef___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_Lean_mkIdentFromRef(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_mkCIdentFrom___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_internal", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_mkCIdentFrom___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkCIdentFrom___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Lean_mkCIdentFrom___closed__1;
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_6 = l_Lean_addMacroScope(x_4, x_2, x_5);
x_7 = l_Lean_SourceInfo_fromRef(x_1, x_3);
x_8 = 1;
lean_inc(x_6);
x_9 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(x_6, x_8);
x_10 = lean_string_utf8_byte_size(x_9);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_6);
lean_ctor_set(x_15, 3, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_mkCIdentFrom(x_1, x_2, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_mkCIdentFrom(x_4, x_1, x_2);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_mkCIdentFromRef___redArg___lam__0(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_box(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_mkCIdentFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Lean_mkCIdentFromRef___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkCIdentFromRef___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdentFromRef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_Lean_mkCIdentFromRef(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = 0;
x_4 = l_Lean_mkCIdentFrom(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_mk_syntax_ident(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_box(2);
x_3 = 1;
lean_inc(x_1);
x_4 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(x_1, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_mkGroupNode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("group", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_mkGroupNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkGroupNode___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkGroupNode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_mkGroupNode___closed__1;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_19; uint8_t x_20; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_10 = x_6;
} else {
 lean_dec_ref(x_6);
 x_10 = lean_box(0);
}
x_19 = lean_array_uget(x_3, x_5);
x_20 = lean_nat_dec_lt(x_1, x_8);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_array_push(x_9, x_19);
x_11 = x_21;
goto block_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_inc(x_2);
x_22 = lean_array_push(x_9, x_2);
x_23 = lean_array_push(x_22, x_19);
x_11 = x_23;
goto block_18;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
if (lean_is_scalar(x_10)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_10;
}
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = 1;
x_16 = lean_usize_add(x_5, x_15);
x_5 = x_16;
x_6 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_mkSepArray___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkSepArray___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkSepArray___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_mkSepArray___closed__1;
x_5 = lean_array_size(x_1);
x_6 = 0;
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_mkSepArray_spec__0(x_3, x_2, x_1, x_5, x_6, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSepArray___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkSepArray(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkOptionalNode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_mkOptionalNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkOptionalNode___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkOptionalNode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_mkSepArray___closed__0;
x_2 = l_Lean_mkOptionalNode___closed__1;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_mkOptionalNode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOptionalNode(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_mkOptionalNode___closed__2;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_mkOptionalNode___closed__3;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_Lean_mkOptionalNode___closed__1;
x_7 = lean_box(2);
x_8 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_5);
return x_8;
}
}
}
static lean_object* _init_l_Lean_mkHole___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hole", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_mkHole___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_mkHole___closed__0;
x_2 = l_Lean_expandMacros___lam__0___closed__2;
x_3 = l_Lean_expandMacros___lam__0___closed__1;
x_4 = l_Lean_expandMacros___lam__0___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_mkHole___closed__1;
x_4 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0;
x_5 = l_Lean_mkAtomFrom(x_1, x_4, x_2);
x_6 = l_Lean_mkOptionalNode___closed__3;
x_7 = lean_array_push(x_6, x_5);
x_8 = lean_box(2);
x_9 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHole___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_mkHole(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_mkSepArray(x_1, x_2);
x_4 = l_Lean_mkOptionalNode___closed__1;
x_5 = lean_box(2);
x_6 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkSep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_mkSep(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_SepArray_ofElems___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_SepArray_ofElems___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Syntax_SepArray_ofElems___closed__0;
x_2 = l_Lean_mkOptionalNode___closed__1;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc_ref(x_1);
x_3 = lean_string_isempty(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_mkAtom(x_1);
x_5 = l_Lean_mkSepArray(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_1);
x_6 = l_Lean_Syntax_SepArray_ofElems___closed__1;
x_7 = l_Lean_mkSepArray(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElems___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_SepArray_ofElems(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_9; 
lean_inc_ref(x_3);
x_9 = lean_string_isempty(x_3);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_mkAtomFrom(x_4, x_3, x_9);
x_5 = x_10;
goto block_8;
}
else
{
lean_object* x_11; 
lean_dec_ref(x_3);
x_11 = l_Lean_Syntax_SepArray_ofElems___closed__1;
x_5 = x_11;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_mkSepArray(x_1, x_5);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_3);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_ofElemsUsingRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_SepArray_ofElemsUsingRef___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeArraySepArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_ofElems___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_SepArray_ofElems(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_TSepArray_ofElems___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_SepArray_ofElems(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_ofElems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_TSepArray_ofElems(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayTSepArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_ofElems___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Syntax_mkApp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Syntax_mkApp___closed__0;
x_2 = l_Lean_expandMacros___lam__0___closed__2;
x_3 = l_Lean_expandMacros___lam__0___closed__1;
x_4 = l_Lean_expandMacros___lam__0___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Syntax_mkApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkApp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Syntax_mkApp___closed__1;
x_7 = l_Lean_mkOptionalNode___closed__1;
x_8 = lean_box(2);
x_9 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_2);
x_10 = l_Lean_Syntax_mkApp___closed__2;
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_array_push(x_11, x_9);
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
else
{
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCApp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_mkCIdent(x_1);
x_4 = l_Lean_Syntax_mkApp(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkLit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Lean_mkOptionalNode___closed__3;
x_6 = lean_array_push(x_5, x_4);
x_7 = lean_box(2);
x_8 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Syntax_mkCharLit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("char", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkCharLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_mkCharLit___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Syntax_mkCharLit___closed__1;
x_4 = l_Char_quote(x_1);
x_5 = l_Lean_Syntax_mkLit(x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkCharLit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Syntax_mkCharLit(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_mkStrLit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkStrLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_mkStrLit___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkStrLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Syntax_mkStrLit___closed__1;
x_4 = l_String_quote(x_1);
x_5 = l_Lean_Syntax_mkLit(x_3, x_4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Syntax_mkNumLit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkNumLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_mkNumLit___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNumLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_mkNumLit___closed__1;
x_4 = l_Lean_Syntax_mkLit(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNatLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Syntax_mkNumLit___closed__1;
x_4 = l_Nat_reprFast(x_1);
x_5 = l_Lean_Syntax_mkLit(x_3, x_4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Syntax_mkScientificLit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scientific", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkScientificLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_mkScientificLit___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkScientificLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_mkScientificLit___closed__1;
x_4 = l_Lean_Syntax_mkLit(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_mkNameLit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_mkNameLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_mkNameLit___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkNameLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_mkNameLit___closed__1;
x_4 = l_Lean_Syntax_mkLit(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_2);
x_6 = 48;
x_7 = lean_uint32_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 49;
x_9 = lean_uint32_dec_eq(x_5, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 95;
x_11 = lean_uint32_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_2 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_mul(x_16, x_3);
lean_dec(x_3);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_17);
x_2 = x_15;
x_3 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_mul(x_22, x_3);
lean_dec(x_3);
x_2 = x_21;
x_3 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; 
lean_dec(x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_3);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; uint32_t x_21; uint8_t x_22; 
x_5 = lean_string_utf8_get(x_1, x_2);
x_21 = 48;
x_22 = lean_uint32_dec_le(x_21, x_5);
if (x_22 == 0)
{
x_6 = x_22;
goto block_20;
}
else
{
uint32_t x_23; uint8_t x_24; 
x_23 = 55;
x_24 = lean_uint32_dec_le(x_5, x_23);
x_6 = x_24;
goto block_20;
}
block_20:
{
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 95;
x_8 = lean_uint32_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(8u);
x_14 = lean_nat_mul(x_13, x_3);
lean_dec(x_3);
x_15 = lean_uint32_to_nat(x_5);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(48u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_2 = x_12;
x_3 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_3);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; uint8_t x_5; uint8_t x_15; uint8_t x_28; uint32_t x_39; uint8_t x_40; 
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = lean_string_utf8_next(x_1, x_2);
x_39 = 48;
x_40 = lean_uint32_dec_le(x_39, x_3);
if (x_40 == 0)
{
x_28 = x_40;
goto block_38;
}
else
{
uint32_t x_41; uint8_t x_42; 
x_41 = 57;
x_42 = lean_uint32_dec_le(x_3, x_41);
x_28 = x_42;
goto block_38;
}
block_14:
{
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_unsigned_to_nat(10u);
x_8 = lean_uint32_to_nat(x_3);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(65u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
block_27:
{
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 65;
x_17 = lean_uint32_dec_le(x_16, x_3);
if (x_17 == 0)
{
x_5 = x_17;
goto block_14;
}
else
{
uint32_t x_18; uint8_t x_19; 
x_18 = 70;
x_19 = lean_uint32_dec_le(x_3, x_18);
x_5 = x_19;
goto block_14;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_unsigned_to_nat(10u);
x_21 = lean_uint32_to_nat(x_3);
x_22 = lean_nat_add(x_20, x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(97u);
x_24 = lean_nat_sub(x_22, x_23);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
block_38:
{
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; 
x_29 = 97;
x_30 = lean_uint32_dec_le(x_29, x_3);
if (x_30 == 0)
{
x_15 = x_30;
goto block_27;
}
else
{
uint32_t x_31; uint8_t x_32; 
x_31 = 102;
x_32 = lean_uint32_dec_le(x_3, x_31);
x_15 = x_32;
goto block_27;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_uint32_to_nat(x_3);
x_34 = lean_unsigned_to_nat(48u);
x_35 = lean_nat_sub(x_33, x_34);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_4);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_2);
x_7 = 95;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_nat_mul(x_15, x_3);
lean_dec(x_3);
x_17 = lean_nat_add(x_16, x_13);
lean_dec(x_13);
lean_dec(x_16);
x_2 = x_14;
x_3 = x_17;
goto _start;
}
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_3);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; uint32_t x_21; uint8_t x_22; 
x_5 = lean_string_utf8_get(x_1, x_2);
x_21 = 48;
x_22 = lean_uint32_dec_le(x_21, x_5);
if (x_22 == 0)
{
x_6 = x_22;
goto block_20;
}
else
{
uint32_t x_23; uint8_t x_24; 
x_23 = 57;
x_24 = lean_uint32_dec_le(x_5, x_23);
x_6 = x_24;
goto block_20;
}
block_20:
{
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 95;
x_8 = lean_uint32_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(10u);
x_14 = lean_nat_mul(x_13, x_3);
lean_dec(x_3);
x_15 = lean_uint32_to_nat(x_5);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(48u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_2 = x_12;
x_3 = x_18;
goto _start;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_3);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_decodeNatLitVal_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_17; uint8_t x_21; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_2, x_3);
if (x_21 == 0)
{
uint32_t x_22; uint32_t x_23; uint8_t x_24; 
x_22 = lean_string_utf8_get(x_1, x_3);
x_23 = 48;
x_24 = lean_uint32_dec_eq(x_22, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = lean_uint32_dec_le(x_23, x_22);
if (x_25 == 0)
{
x_17 = x_25;
goto block_20;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 57;
x_27 = lean_uint32_dec_le(x_22, x_26);
x_17 = x_27;
goto block_20;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_eq(x_2, x_28);
lean_dec(x_2);
if (x_29 == 0)
{
uint32_t x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_string_utf8_get(x_1, x_28);
x_31 = 120;
x_32 = lean_uint32_dec_eq(x_30, x_31);
if (x_32 == 0)
{
uint32_t x_33; uint8_t x_34; 
x_33 = 88;
x_34 = lean_uint32_dec_eq(x_30, x_33);
if (x_34 == 0)
{
uint32_t x_35; uint8_t x_36; 
x_35 = 98;
x_36 = lean_uint32_dec_eq(x_30, x_35);
if (x_36 == 0)
{
uint32_t x_37; uint8_t x_38; 
x_37 = 66;
x_38 = lean_uint32_dec_eq(x_30, x_37);
if (x_38 == 0)
{
uint32_t x_39; uint8_t x_40; 
x_39 = 111;
x_40 = lean_uint32_dec_eq(x_30, x_39);
if (x_40 == 0)
{
uint32_t x_41; uint8_t x_42; 
x_41 = 79;
x_42 = lean_uint32_dec_eq(x_30, x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = lean_uint32_dec_le(x_23, x_30);
if (x_43 == 0)
{
x_4 = x_43;
goto block_7;
}
else
{
uint32_t x_44; uint8_t x_45; 
x_44 = 57;
x_45 = lean_uint32_dec_le(x_30, x_44);
x_4 = x_45;
goto block_7;
}
}
else
{
goto block_10;
}
}
else
{
goto block_10;
}
}
else
{
goto block_13;
}
}
else
{
goto block_13;
}
}
else
{
goto block_16;
}
}
else
{
goto block_16;
}
}
else
{
lean_object* x_46; 
x_46 = l_Lean_Syntax_decodeNatLitVal_x3f___closed__0;
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_2);
x_47 = lean_box(0);
return x_47;
}
block_7:
{
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(x_1, x_3, x_3);
return x_6;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeOctalLitAux(x_1, x_8, x_3);
return x_9;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeBinLitAux(x_1, x_11, x_3);
return x_12;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(x_1, x_14, x_3);
return x_15;
}
block_20:
{
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeDecimalLitAux(x_1, x_3, x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNatLitVal_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeNatLitVal_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_name_eq(x_3, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fget_borrowed(x_4, x_11);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
}
}
}
else
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isLit_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isLit_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Syntax_decodeNatLitVal_x3f(x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_mkNumLit___closed__1;
x_3 = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_isFieldIdx_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fieldIdx", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_isFieldIdx_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_isFieldIdx_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isFieldIdx_x3f___closed__1;
x_3 = l___private_Init_Meta_Defs_0__Lean_Syntax_isNatLitAux(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isFieldIdx_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_1, x_2);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; uint32_t x_24; uint8_t x_25; 
x_8 = lean_string_utf8_get(x_1, x_2);
x_24 = 48;
x_25 = lean_uint32_dec_le(x_24, x_8);
if (x_25 == 0)
{
x_9 = x_25;
goto block_23;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 57;
x_27 = lean_uint32_dec_le(x_8, x_26);
x_9 = x_27;
goto block_23;
}
block_23:
{
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 95;
x_11 = lean_uint32_dec_eq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_2 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(10u);
x_17 = lean_nat_mul(x_16, x_6);
lean_dec(x_6);
x_18 = lean_uint32_to_nat(x_8);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(48u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_2 = x_15;
x_6 = x_21;
goto _start;
}
}
}
else
{
lean_dec(x_2);
if (x_5 == 0)
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_4, x_6);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_nat_sub(x_4, x_6);
lean_dec(x_6);
x_30 = lean_box(x_7);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_nat_sub(x_6, x_4);
lean_dec(x_6);
x_35 = lean_box(x_5);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_nat_add(x_6, x_4);
lean_dec(x_6);
x_40 = lean_box(x_5);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
x_8 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(x_1, x_2, x_3, x_4, x_7, x_6);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_2);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_2);
x_7 = 45;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 43;
x_10 = lean_uint32_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(x_1, x_2, x_3, x_4, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(x_1, x_13, x_3, x_4, x_8, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterExp(x_1, x_16, x_3, x_4, x_8, x_17);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_1, x_2);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; uint32_t x_31; uint8_t x_32; 
x_9 = lean_string_utf8_get(x_1, x_2);
x_31 = 48;
x_32 = lean_uint32_dec_le(x_31, x_9);
if (x_32 == 0)
{
x_10 = x_32;
goto block_30;
}
else
{
uint32_t x_33; uint8_t x_34; 
x_33 = 57;
x_34 = lean_uint32_dec_le(x_9, x_33);
x_10 = x_34;
goto block_30;
}
block_30:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 95;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 101;
x_14 = lean_uint32_dec_eq(x_9, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 69;
x_16 = lean_uint32_dec_eq(x_9, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_box(0);
return x_17;
}
else
{
goto block_7;
}
}
else
{
goto block_7;
}
}
else
{
lean_object* x_18; 
x_18 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_21 = lean_unsigned_to_nat(10u);
x_22 = lean_nat_mul(x_21, x_3);
lean_dec(x_3);
x_23 = lean_uint32_to_nat(x_9);
x_24 = lean_nat_add(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(48u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_4, x_27);
lean_dec(x_4);
x_2 = x_20;
x_3 = x_26;
x_4 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_35 = lean_box(x_8);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_4);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_6 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_1, x_2);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; uint32_t x_34; uint8_t x_35; 
x_9 = lean_string_utf8_get(x_1, x_2);
x_34 = 48;
x_35 = lean_uint32_dec_le(x_34, x_9);
if (x_35 == 0)
{
x_10 = x_35;
goto block_33;
}
else
{
uint32_t x_36; uint8_t x_37; 
x_36 = 57;
x_37 = lean_uint32_dec_le(x_9, x_36);
x_10 = x_37;
goto block_33;
}
block_33:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 95;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 46;
x_14 = lean_uint32_dec_eq(x_9, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 101;
x_16 = lean_uint32_dec_eq(x_9, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 69;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
return x_19;
}
else
{
goto block_7;
}
}
else
{
goto block_7;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeAfterDot(x_1, x_20, x_3, x_21);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_2 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_26 = lean_unsigned_to_nat(10u);
x_27 = lean_nat_mul(x_26, x_3);
lean_dec(x_3);
x_28 = lean_uint32_to_nat(x_9);
x_29 = lean_nat_add(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(48u);
x_31 = lean_nat_sub(x_29, x_30);
lean_dec(x_29);
x_2 = x_25;
x_3 = x_31;
goto _start;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
return x_38;
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decodeExp(x_1, x_4, x_3, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_8; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get(x_1, x_3);
x_10 = 48;
x_11 = lean_uint32_dec_le(x_10, x_9);
if (x_11 == 0)
{
x_4 = x_11;
goto block_7;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 57;
x_13 = lean_uint32_dec_le(x_9, x_12);
x_4 = x_13;
goto block_7;
}
}
else
{
lean_object* x_14; 
x_14 = lean_box(0);
return x_14;
}
block_7:
{
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeScientificLitVal_x3f_decode(x_1, x_3, x_3);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeScientificLitVal_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeScientificLitVal_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_mkScientificLit___closed__1;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Syntax_decodeScientificLitVal_x3f(x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isScientificLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isScientificLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 3:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_substring_tostring(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
default: 
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isNatLit_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_toNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_toNat(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 9;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 13;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 39;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; uint32_t x_5; uint8_t x_6; 
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = lean_string_utf8_next(x_1, x_2);
x_5 = 92;
x_6 = lean_uint32_dec_eq(x_3, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 34;
x_8 = lean_uint32_dec_eq(x_3, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 39;
x_10 = lean_uint32_dec_eq(x_3, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 114;
x_12 = lean_uint32_dec_eq(x_3, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 110;
x_14 = lean_uint32_dec_eq(x_3, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 116;
x_16 = lean_uint32_dec_eq(x_3, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 120;
x_18 = lean_uint32_dec_eq(x_3, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 117;
x_20 = lean_uint32_dec_eq(x_3, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_4);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(x_1, x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_25);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(x_1, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_25);
x_33 = lean_box(0);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(x_1, x_36);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
x_38 = lean_box(0);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_unsigned_to_nat(16u);
x_44 = lean_nat_mul(x_43, x_25);
lean_dec(x_25);
x_45 = lean_nat_add(x_44, x_30);
lean_dec(x_30);
lean_dec(x_44);
x_46 = lean_nat_mul(x_43, x_45);
lean_dec(x_45);
x_47 = lean_nat_add(x_46, x_35);
lean_dec(x_35);
lean_dec(x_46);
x_48 = lean_nat_mul(x_43, x_47);
lean_dec(x_47);
x_49 = lean_nat_add(x_48, x_42);
lean_dec(x_42);
lean_dec(x_48);
x_50 = l_Char_ofNat(x_49);
lean_dec(x_49);
x_51 = lean_box_uint32(x_50);
lean_ctor_set(x_40, 0, x_51);
return x_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint32_t x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_unsigned_to_nat(16u);
x_55 = lean_nat_mul(x_54, x_25);
lean_dec(x_25);
x_56 = lean_nat_add(x_55, x_30);
lean_dec(x_30);
lean_dec(x_55);
x_57 = lean_nat_mul(x_54, x_56);
lean_dec(x_56);
x_58 = lean_nat_add(x_57, x_35);
lean_dec(x_35);
lean_dec(x_57);
x_59 = lean_nat_mul(x_54, x_58);
lean_dec(x_58);
x_60 = lean_nat_add(x_59, x_52);
lean_dec(x_52);
lean_dec(x_59);
x_61 = l_Char_ofNat(x_60);
lean_dec(x_60);
x_62 = lean_box_uint32(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_53);
lean_ctor_set(x_37, 0, x_63);
return x_37;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint32_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_64 = lean_ctor_get(x_37, 0);
lean_inc(x_64);
lean_dec(x_37);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_unsigned_to_nat(16u);
x_69 = lean_nat_mul(x_68, x_25);
lean_dec(x_25);
x_70 = lean_nat_add(x_69, x_30);
lean_dec(x_30);
lean_dec(x_69);
x_71 = lean_nat_mul(x_68, x_70);
lean_dec(x_70);
x_72 = lean_nat_add(x_71, x_35);
lean_dec(x_35);
lean_dec(x_71);
x_73 = lean_nat_mul(x_68, x_72);
lean_dec(x_72);
x_74 = lean_nat_add(x_73, x_65);
lean_dec(x_65);
lean_dec(x_73);
x_75 = l_Char_ofNat(x_74);
lean_dec(x_74);
x_76 = lean_box_uint32(x_75);
if (lean_is_scalar(x_67)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_67;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_66);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
}
}
}
else
{
lean_object* x_79; 
x_79 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_box(0);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexDigit(x_1, x_83);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
lean_dec(x_82);
x_85 = lean_box(0);
return x_85;
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint32_t x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_unsigned_to_nat(16u);
x_91 = lean_nat_mul(x_90, x_82);
lean_dec(x_82);
x_92 = lean_nat_add(x_91, x_89);
lean_dec(x_89);
lean_dec(x_91);
x_93 = l_Char_ofNat(x_92);
lean_dec(x_92);
x_94 = lean_box_uint32(x_93);
lean_ctor_set(x_87, 0, x_94);
return x_84;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint32_t x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get(x_87, 0);
x_96 = lean_ctor_get(x_87, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_87);
x_97 = lean_unsigned_to_nat(16u);
x_98 = lean_nat_mul(x_97, x_82);
lean_dec(x_82);
x_99 = lean_nat_add(x_98, x_95);
lean_dec(x_95);
lean_dec(x_98);
x_100 = l_Char_ofNat(x_99);
lean_dec(x_99);
x_101 = lean_box_uint32(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
lean_ctor_set(x_84, 0, x_102);
return x_84;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint32_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_84, 0);
lean_inc(x_103);
lean_dec(x_84);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = lean_unsigned_to_nat(16u);
x_108 = lean_nat_mul(x_107, x_82);
lean_dec(x_82);
x_109 = lean_nat_add(x_108, x_104);
lean_dec(x_104);
lean_dec(x_108);
x_110 = l_Char_ofNat(x_109);
lean_dec(x_109);
x_111 = lean_box_uint32(x_110);
if (lean_is_scalar(x_106)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_106;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_105);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_4);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_4);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_4);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_4);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_4);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_4);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_decodeQuotedChar(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_decodeStringGap___lam__0(uint32_t x_1) {
_start:
{
uint8_t x_2; uint32_t x_8; uint8_t x_9; 
x_8 = 32;
x_9 = lean_uint32_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 9;
x_11 = lean_uint32_dec_eq(x_1, x_10);
x_2 = x_11;
goto block_7;
}
else
{
x_2 = x_9;
goto block_7;
}
block_7:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 13;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 10;
x_6 = lean_uint32_dec_eq(x_1, x_5);
return x_6;
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Syntax_decodeStringGap___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_decodeStringGap___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeStringGap___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_8; uint32_t x_11; uint8_t x_12; uint32_t x_18; uint8_t x_19; 
x_3 = l_Lean_Syntax_decodeStringGap___closed__0;
x_11 = lean_string_utf8_get(x_1, x_2);
x_18 = 32;
x_19 = lean_uint32_dec_eq(x_11, x_18);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 9;
x_21 = lean_uint32_dec_eq(x_11, x_20);
x_12 = x_21;
goto block_17;
}
else
{
x_12 = x_19;
goto block_17;
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_utf8_next(x_1, x_2);
x_5 = lean_string_nextwhile(x_1, x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
block_10:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
goto block_7;
}
}
block_17:
{
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 13;
x_14 = lean_uint32_dec_eq(x_11, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 10;
x_16 = lean_uint32_dec_eq(x_11, x_15);
x_8 = x_16;
goto block_10;
}
else
{
x_8 = x_14;
goto block_10;
}
}
else
{
goto block_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStringGap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_decodeStringGap(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = 34;
x_6 = lean_uint32_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_8 = lean_string_utf8_at_end(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 92;
x_10 = lean_uint32_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_string_push(x_3, x_4);
x_2 = x_7;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Syntax_decodeQuotedChar(x_1, x_7);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; 
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unbox_uint32(x_15);
lean_dec(x_15);
x_18 = lean_string_push(x_3, x_17);
x_2 = x_16;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_13);
lean_inc_ref(x_1);
x_20 = l_Lean_Syntax_decodeStringGap(x_1, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_2 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_24 = lean_box(0);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_3);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_6 = 35;
x_7 = lean_uint32_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_string_utf8_byte_size(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_11 = lean_nat_sub(x_8, x_10);
lean_dec(x_10);
x_12 = lean_string_utf8_extract(x_1, x_5, x_11);
lean_dec(x_11);
lean_dec(x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_2 = x_5;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeRawStrLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_decodeRawStrLitAux(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 114;
x_5 = lean_uint32_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_versionString___closed__0;
x_8 = l_Lean_Syntax_decodeStrLitAux(x_1, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_decodeRawStrLitAux(x_1, x_9, x_2);
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_mkStrLit___closed__1;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Syntax_decodeStrLit(x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isStrLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 92;
x_5 = lean_uint32_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box_uint32(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_decodeQuotedChar(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeCharLit(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_mkCharLit___closed__1;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Syntax_decodeCharLit(x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isCharLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_14; uint32_t x_25; uint8_t x_26; 
x_25 = 65;
x_26 = lean_uint32_dec_le(x_25, x_1);
if (x_26 == 0)
{
goto block_24;
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = 90;
x_28 = lean_uint32_dec_le(x_1, x_27);
if (x_28 == 0)
{
goto block_24;
}
else
{
return x_28;
}
}
block_13:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 95;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 39;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 33;
x_8 = lean_uint32_dec_eq(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 63;
x_10 = lean_uint32_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_isLetterLike(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_isSubScriptAlnum(x_1);
return x_12;
}
else
{
return x_11;
}
}
else
{
return x_10;
}
}
else
{
return x_8;
}
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_19:
{
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 48;
x_16 = lean_uint32_dec_le(x_15, x_1);
if (x_16 == 0)
{
x_2 = x_16;
goto block_13;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 57;
x_18 = lean_uint32_dec_le(x_1, x_17);
x_2 = x_18;
goto block_13;
}
}
else
{
return x_14;
}
}
block_24:
{
uint32_t x_20; uint8_t x_21; 
x_20 = 97;
x_21 = lean_uint32_dec_le(x_20, x_1);
if (x_21 == 0)
{
x_14 = x_21;
goto block_19;
}
else
{
uint32_t x_22; uint8_t x_23; 
x_22 = 122;
x_23 = lean_uint32_dec_le(x_1, x_22);
x_14 = x_23;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 57;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(uint8_t x_1, uint8_t x_2, uint32_t x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 187;
x_5 = lean_uint32_dec_eq(x_3, x_4);
if (x_5 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint32_t x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2(x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_14; 
lean_inc_ref(x_1);
x_14 = lean_substring_isempty(x_1);
if (x_14 == 0)
{
uint32_t x_15; uint32_t x_16; uint8_t x_17; 
lean_inc_ref(x_1);
x_15 = lean_substring_front(x_1);
x_16 = 171;
x_17 = lean_uint32_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_29; uint8_t x_30; uint8_t x_42; uint8_t x_48; uint32_t x_58; uint8_t x_59; 
x_18 = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0;
x_29 = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1;
x_58 = 65;
x_59 = lean_uint32_dec_le(x_58, x_15);
if (x_59 == 0)
{
goto block_57;
}
else
{
uint32_t x_60; uint8_t x_61; 
x_60 = 90;
x_61 = lean_uint32_dec_le(x_15, x_60);
if (x_61 == 0)
{
goto block_57;
}
else
{
goto block_28;
}
}
block_28:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_1);
x_19 = lean_substring_takewhile(x_1, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_nat_sub(x_21, x_20);
lean_dec(x_20);
lean_dec(x_21);
x_25 = lean_nat_sub(x_23, x_22);
x_26 = lean_substring_extract(x_1, x_24, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_2);
x_3 = x_26;
x_4 = x_27;
goto block_13;
}
block_41:
{
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_31 = lean_box(0);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc_ref(x_1);
x_32 = lean_substring_takewhile(x_1, x_29);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_nat_sub(x_34, x_33);
lean_dec(x_33);
lean_dec(x_34);
x_38 = lean_nat_sub(x_36, x_35);
x_39 = lean_substring_extract(x_1, x_37, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_2);
x_3 = x_39;
x_4 = x_40;
goto block_13;
}
}
block_47:
{
if (x_42 == 0)
{
uint32_t x_43; uint8_t x_44; 
x_43 = 48;
x_44 = lean_uint32_dec_le(x_43, x_15);
if (x_44 == 0)
{
x_30 = x_44;
goto block_41;
}
else
{
uint32_t x_45; uint8_t x_46; 
x_45 = 57;
x_46 = lean_uint32_dec_le(x_15, x_45);
x_30 = x_46;
goto block_41;
}
}
else
{
goto block_28;
}
}
block_52:
{
if (x_48 == 0)
{
uint32_t x_49; uint8_t x_50; 
x_49 = 95;
x_50 = lean_uint32_dec_eq(x_15, x_49);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_isLetterLike(x_15);
x_42 = x_51;
goto block_47;
}
else
{
x_42 = x_50;
goto block_47;
}
}
else
{
goto block_28;
}
}
block_57:
{
uint32_t x_53; uint8_t x_54; 
x_53 = 97;
x_54 = lean_uint32_dec_le(x_53, x_15);
if (x_54 == 0)
{
x_48 = x_54;
goto block_52;
}
else
{
uint32_t x_55; uint8_t x_56; 
x_55 = 122;
x_56 = lean_uint32_dec_le(x_15, x_55);
x_48 = x_56;
goto block_52;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_box(x_17);
x_63 = lean_box(x_14);
x_64 = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___lam__2___boxed), 3, 2);
lean_closure_set(x_64, 0, x_62);
lean_closure_set(x_64, 1, x_63);
lean_inc_ref(x_1);
x_65 = lean_substring_takewhile(x_1, x_64);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_81; uint32_t x_82; uint32_t x_83; uint8_t x_84; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
x_69 = lean_ctor_get(x_65, 2);
x_70 = lean_ctor_get(x_1, 1);
x_71 = lean_ctor_get(x_1, 2);
x_72 = lean_string_utf8_next(x_67, x_69);
lean_dec(x_69);
lean_inc(x_71);
x_73 = lean_string_pos_min(x_71, x_72);
lean_inc(x_73);
lean_inc(x_68);
lean_ctor_set(x_65, 2, x_73);
x_74 = lean_nat_sub(x_73, x_68);
lean_dec(x_68);
lean_dec(x_73);
lean_inc(x_74);
lean_inc_ref(x_65);
x_81 = lean_substring_prev(x_65, x_74);
lean_inc_ref(x_65);
x_82 = lean_substring_get(x_65, x_81);
x_83 = 187;
x_84 = lean_uint32_dec_eq(x_82, x_83);
if (x_84 == 0)
{
x_75 = x_17;
goto block_80;
}
else
{
x_75 = x_14;
goto block_80;
}
block_80:
{
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_nat_sub(x_71, x_70);
x_77 = lean_substring_extract(x_1, x_74, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_65);
lean_ctor_set(x_78, 1, x_2);
x_3 = x_77;
x_4 = x_78;
goto block_13;
}
else
{
lean_object* x_79; 
lean_dec(x_74);
lean_dec_ref(x_65);
lean_dec(x_2);
lean_dec_ref(x_1);
x_79 = lean_box(0);
return x_79;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_100; uint32_t x_101; uint32_t x_102; uint8_t x_103; 
x_85 = lean_ctor_get(x_65, 0);
x_86 = lean_ctor_get(x_65, 1);
x_87 = lean_ctor_get(x_65, 2);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_65);
x_88 = lean_ctor_get(x_1, 1);
x_89 = lean_ctor_get(x_1, 2);
x_90 = lean_string_utf8_next(x_85, x_87);
lean_dec(x_87);
lean_inc(x_89);
x_91 = lean_string_pos_min(x_89, x_90);
lean_inc(x_91);
lean_inc(x_86);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_86);
lean_ctor_set(x_92, 2, x_91);
x_93 = lean_nat_sub(x_91, x_86);
lean_dec(x_86);
lean_dec(x_91);
lean_inc(x_93);
lean_inc_ref(x_92);
x_100 = lean_substring_prev(x_92, x_93);
lean_inc_ref(x_92);
x_101 = lean_substring_get(x_92, x_100);
x_102 = 187;
x_103 = lean_uint32_dec_eq(x_101, x_102);
if (x_103 == 0)
{
x_94 = x_17;
goto block_99;
}
else
{
x_94 = x_14;
goto block_99;
}
block_99:
{
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_nat_sub(x_89, x_88);
x_96 = lean_substring_extract(x_1, x_93, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_2);
x_3 = x_96;
x_4 = x_97;
goto block_13;
}
else
{
lean_object* x_98; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_2);
lean_dec_ref(x_1);
x_98 = lean_box(0);
return x_98;
}
}
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_104 = lean_box(0);
return x_104;
}
block_13:
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
lean_inc_ref(x_3);
x_5 = lean_substring_front(x_3);
x_6 = 46;
x_7 = lean_uint32_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_substring_isempty(x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_box(0);
return x_9;
}
else
{
return x_4;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_substring_drop(x_3, x_10);
x_1 = x_11;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_splitNameLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(x_1, x_2);
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Meta.Defs", 14, 14);
return x_1;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Substring.Raw.toName", 20, 20);
return x_1;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2;
x_2 = lean_unsigned_to_nat(10u);
x_3 = lean_unsigned_to_nat(1133u);
x_4 = l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1;
x_5 = l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint32_t x_15; uint32_t x_16; uint8_t x_17; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_List_foldr___at___00Substring_Raw_toName_spec__0(x_1, x_4);
x_6 = lean_substring_tostring(x_3);
lean_inc_ref(x_6);
x_15 = lean_string_front(x_6);
x_16 = 171;
x_17 = lean_uint32_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 48;
x_19 = lean_uint32_dec_le(x_18, x_15);
if (x_19 == 0)
{
x_7 = x_19;
goto block_14;
}
else
{
uint32_t x_20; uint8_t x_21; 
x_20 = 57;
x_21 = lean_uint32_dec_le(x_15, x_20);
x_7 = x_21;
goto block_14;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_string_drop(x_6, x_22);
x_24 = lean_string_dropright(x_23, x_22);
x_25 = l_Lean_Name_str___override(x_5, x_24);
return x_25;
}
block_14:
{
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Name_str___override(x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Syntax_decodeNatLitVal_x3f(x_6);
lean_dec_ref(x_6);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Name_num___override(x_5, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3;
x_13 = l_panic___at___00__private_Init_Prelude_0__Lean_assembleParts_spec__0(x_12);
return x_13;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Substring_Raw_toName_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldr___at___00Substring_Raw_toName_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_toName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_List_foldr___at___00Substring_Raw_toName_spec__0(x_5, x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_String_toName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_Substring_Raw_toName(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_decodeNameLit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 96;
x_5 = lean_uint32_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_string_utf8_byte_size(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_substring_drop(x_8, x_9);
x_11 = l_Substring_Raw_toName(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_mkNameLit___closed__1;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Syntax_decodeNameLit(x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isNameLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasArgs(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_hasArgs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAtom(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isAtom(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isToken(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = lean_string_trim(x_3);
x_5 = lean_string_trim(x_1);
x_6 = lean_string_dec_eq(x_4, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isToken___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_isToken(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isNone(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_mkOptionalNode___closed__1;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
return x_8;
}
}
case 0:
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
default: 
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isNone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isNone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptional_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_Syntax_getId(x_5);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptionalIdent_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = l_Lean_Syntax_getHead_x3f___closed__0;
x_9 = lean_array_size(x_3);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(x_1, x_7, x_8, x_3, x_9, x_10, x_8);
lean_dec_ref(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 0)
{
return x_6;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_inc(x_2);
x_15 = lean_apply_1(x_1, x_2);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec_ref(x_1);
lean_inc_ref(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_4, x_6);
lean_inc_ref(x_1);
x_10 = l_Lean_Syntax_findAux(x_1, x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
else
{
size_t x_13; size_t x_14; 
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
{
size_t _tmp_5 = x_14;
lean_object* _tmp_6 = x_3;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_findAux_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_findAux(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isNatLit_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_getNat(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hexnum", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeHexLitAux(x_4, x_5, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumVal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_getHexNumVal(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_string_utf8_next(x_1, x_2);
x_6 = lean_string_utf8_get(x_1, x_2);
lean_dec(x_2);
x_7 = 95;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_2 = x_5;
x_3 = x_10;
goto _start;
}
else
{
x_2 = x_5;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Init_Meta_Defs_0__Lean_TSyntax_getHexNumSize_go(x_4, x_5, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(0u);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHexNumSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_getHexNumSize(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getId(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_getId(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TSyntax_getScientific___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_TSyntax_getScientific___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_TSyntax_getScientific___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isScientificLit_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_TSyntax_getScientific___closed__1;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getScientific___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_getScientific(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isStrLit_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_versionString___closed__0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_getString(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_Lean_TSyntax_getChar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isCharLit_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint32_t x_3; 
x_3 = 65;
return x_3;
}
else
{
lean_object* x_4; uint32_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_unbox_uint32(x_4);
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Lean_TSyntax_getChar(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isNameLit_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_getName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getHygieneInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_getHygieneInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_SepArray_ofElems(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TSyntax_Compat_instCoeTailArraySyntaxTSepArray(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getId(x_5);
x_7 = l_Lean_extractMacroScopes(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
lean_inc(x_2);
x_10 = lean_erase_macro_scopes(x_2);
lean_ctor_set(x_7, 0, x_10);
x_11 = l_Lean_MacroScopesView_review(x_7);
x_12 = l_Lean_SourceInfo_fromRef(x_5, x_3);
lean_dec(x_5);
x_13 = 1;
x_14 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(x_2, x_13);
x_15 = lean_string_utf8_byte_size(x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set(x_18, 3, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_7, 1);
x_20 = lean_ctor_get(x_7, 2);
x_21 = lean_ctor_get(x_7, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
lean_inc(x_2);
x_22 = lean_erase_macro_scopes(x_2);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
x_24 = l_Lean_MacroScopesView_review(x_23);
x_25 = l_Lean_SourceInfo_fromRef(x_5, x_3);
lean_dec(x_5);
x_26 = 1;
x_27 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken___at___00__private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toString_spec__0(x_2, x_26);
x_28 = lean_string_utf8_byte_size(x_27);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_4);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HygieneInfo_mkIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_HygieneInfo_mkIdent(x_1, x_2, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_instQuoteOfCoeHTCTTSyntaxConsSyntaxNodeKindNil(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_instQuoteTermMkStr1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteTermMkStr1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instQuoteTermMkStr1___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instQuoteBoolMkStr1___lam__0___closed__1;
x_2 = l_Lean_instQuoteBoolMkStr1___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instQuoteBoolMkStr1___lam__0___closed__2;
x_2 = l_Lean_mkCIdent(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instQuoteBoolMkStr1___lam__0___closed__4;
x_2 = l_Lean_instQuoteBoolMkStr1___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instQuoteBoolMkStr1___lam__0___closed__5;
x_2 = l_Lean_mkCIdent(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_instQuoteBoolMkStr1___lam__0___closed__3;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_instQuoteBoolMkStr1___lam__0___closed__6;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteBoolMkStr1___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_instQuoteBoolMkStr1___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instQuoteBoolMkStr1___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteBoolMkStr1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instQuoteBoolMkStr1___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(2);
x_3 = l_Lean_Syntax_mkCharLit(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteCharCharLitKind___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_instQuoteCharCharLitKind___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteCharCharLitKind___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instQuoteCharCharLitKind___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteCharCharLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instQuoteCharCharLitKind___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteStringStrLitKind___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(2);
x_3 = l_Lean_Syntax_mkStrLit(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instQuoteStringStrLitKind___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instQuoteStringStrLitKind___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteStringStrLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instQuoteStringStrLitKind___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNatNumLitKind___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_reprFast(x_1);
x_3 = lean_box(2);
x_4 = l_Lean_Syntax_mkNumLit(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instQuoteNatNumLitKind___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instQuoteNatNumLitKind___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteNatNumLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instQuoteNatNumLitKind___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteRawMkStr1___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteRawMkStr1___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toRawSubstring'", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteRawMkStr1___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instQuoteRawMkStr1___lam__0___closed__1;
x_2 = l_Lean_instQuoteRawMkStr1___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteRawMkStr1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_instQuoteRawMkStr1___lam__0___closed__2;
x_3 = lean_substring_tostring(x_1);
x_4 = lean_box(2);
x_5 = l_Lean_Syntax_mkStrLit(x_3, x_4);
x_6 = l_Lean_mkOptionalNode___closed__3;
x_7 = lean_array_push(x_6, x_5);
x_8 = l_Lean_Syntax_mkCApp(x_2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_instQuoteRawMkStr1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instQuoteRawMkStr1___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteRawMkStr1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instQuoteRawMkStr1___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = l_List_isEmpty___redArg(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_byte_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
x_16 = lean_string_append(x_15, x_7);
lean_dec_ref(x_7);
x_17 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_8 = x_18;
goto block_11;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_33; uint32_t x_35; uint8_t x_36; uint32_t x_41; uint8_t x_47; uint8_t x_57; uint8_t x_58; uint8_t x_62; uint8_t x_68; uint8_t x_69; 
x_19 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1;
x_20 = l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0;
x_57 = lean_string_get_byte_fast(x_7, x_12);
x_68 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2;
x_69 = lean_uint8_dec_le(x_68, x_57);
if (x_69 == 0)
{
x_62 = x_69;
goto block_67;
}
else
{
uint8_t x_70; uint8_t x_71; 
x_70 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3;
x_71 = lean_uint8_dec_le(x_57, x_70);
x_62 = x_71;
goto block_67;
}
block_27:
{
uint8_t x_21; 
lean_inc_ref(x_7);
x_21 = lean_string_any(x_7, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0;
x_23 = lean_string_append(x_22, x_7);
lean_dec_ref(x_7);
x_24 = l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_8 = x_25;
goto block_11;
}
else
{
lean_object* x_26; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_box(0);
return x_26;
}
}
block_32:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_inc_ref(x_7);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_12);
lean_ctor_set(x_28, 2, x_13);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_substring_drop(x_28, x_29);
x_31 = lean_substring_all(x_30, x_19);
if (x_31 == 0)
{
goto block_27;
}
else
{
x_8 = x_7;
goto block_11;
}
}
block_34:
{
if (x_33 == 0)
{
goto block_27;
}
else
{
goto block_32;
}
}
block_40:
{
if (x_36 == 0)
{
uint32_t x_37; uint8_t x_38; 
x_37 = 95;
x_38 = lean_uint32_dec_eq(x_35, x_37);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_isLetterLike(x_35);
x_33 = x_39;
goto block_34;
}
else
{
x_33 = x_38;
goto block_34;
}
}
else
{
goto block_32;
}
}
block_46:
{
uint32_t x_42; uint8_t x_43; 
x_42 = 97;
x_43 = lean_uint32_dec_le(x_42, x_41);
if (x_43 == 0)
{
x_35 = x_41;
x_36 = x_43;
goto block_40;
}
else
{
uint32_t x_44; uint8_t x_45; 
x_44 = 122;
x_45 = lean_uint32_dec_le(x_41, x_44);
x_35 = x_41;
x_36 = x_45;
goto block_40;
}
}
block_53:
{
if (x_47 == 0)
{
uint32_t x_48; uint32_t x_49; uint8_t x_50; 
x_48 = lean_string_utf8_get(x_7, x_12);
x_49 = 65;
x_50 = lean_uint32_dec_le(x_49, x_48);
if (x_50 == 0)
{
x_41 = x_48;
goto block_46;
}
else
{
uint32_t x_51; uint8_t x_52; 
x_51 = 90;
x_52 = lean_uint32_dec_le(x_48, x_51);
if (x_52 == 0)
{
x_41 = x_48;
goto block_46;
}
else
{
goto block_32;
}
}
}
else
{
x_8 = x_7;
goto block_11;
}
}
block_56:
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscapeAsciiRest(x_7, x_54);
x_47 = x_55;
goto block_53;
}
block_61:
{
if (x_58 == 0)
{
uint8_t x_59; uint8_t x_60; 
x_59 = l_Lean_isIdFirstAscii___closed__0;
x_60 = lean_uint8_dec_eq(x_57, x_59);
if (x_60 == 0)
{
x_47 = x_60;
goto block_53;
}
else
{
goto block_56;
}
}
else
{
goto block_56;
}
}
block_67:
{
if (x_62 == 0)
{
uint8_t x_63; uint8_t x_64; 
x_63 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0;
x_64 = lean_uint8_dec_le(x_63, x_57);
if (x_64 == 0)
{
x_58 = x_64;
goto block_61;
}
else
{
uint8_t x_65; uint8_t x_66; 
x_65 = l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1;
x_66 = lean_uint8_dec_le(x_57, x_65);
x_58 = x_66;
goto block_61;
}
}
else
{
goto block_56;
}
}
}
block_11:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
default: 
{
lean_object* x_72; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_72 = lean_box(0);
return x_72;
}
}
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("anonymous", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_quoteNameMk___closed__1;
x_2 = l_Lean_quoteNameMk___closed__0;
x_3 = l_Lean_expandMacros___lam__0___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_quoteNameMk___closed__2;
x_2 = l_Lean_mkCIdent(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkStr", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_quoteNameMk___closed__4;
x_2 = l_Lean_quoteNameMk___closed__0;
x_3 = l_Lean_expandMacros___lam__0___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkNum", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_quoteNameMk___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_quoteNameMk___closed__6;
x_2 = l_Lean_quoteNameMk___closed__0;
x_3 = l_Lean_expandMacros___lam__0___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_quoteNameMk(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_quoteNameMk___closed__3;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_quoteNameMk___closed__5;
x_6 = l_Lean_quoteNameMk(x_3);
x_7 = lean_box(2);
x_8 = l_Lean_Syntax_mkStrLit(x_4, x_7);
x_9 = l_Lean_Syntax_mkApp___closed__2;
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_array_push(x_10, x_8);
x_12 = l_Lean_Syntax_mkCApp(x_5, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = l_Lean_quoteNameMk___closed__7;
x_16 = l_Lean_quoteNameMk(x_13);
x_17 = l_Nat_reprFast(x_14);
x_18 = lean_box(2);
x_19 = l_Lean_Syntax_mkNumLit(x_17, x_18);
x_20 = l_Lean_Syntax_mkApp___closed__2;
x_21 = lean_array_push(x_20, x_16);
x_22 = lean_array_push(x_21, x_19);
x_23 = l_Lean_Syntax_mkCApp(x_15, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_instQuoteNameMkStr1___private__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quotedName", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteNameMkStr1___private__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_instQuoteNameMkStr1___private__1___closed__0;
x_2 = l_Lean_expandMacros___lam__0___closed__2;
x_3 = l_Lean_expandMacros___lam__0___closed__1;
x_4 = l_Lean_expandMacros___lam__0___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
lean_inc(x_1);
x_3 = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_quoteNameMk(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Lean_instQuoteNameMkStr1___private__1___closed__1;
x_7 = l_Lean_Name_reprPrec___closed__2;
x_8 = l_Lean_versionStringCore___closed__1;
x_9 = lean_string_intercalate(x_8, x_5);
x_10 = lean_string_append(x_7, x_9);
lean_dec_ref(x_9);
x_11 = lean_box(2);
x_12 = l_Lean_Syntax_mkNameLit(x_10, x_11);
x_13 = l_Lean_mkOptionalNode___closed__3;
x_14 = lean_array_push(x_13, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_instQuoteNameMkStr1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instQuoteNameMkStr1___private__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteNameMkStr1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instQuoteNameMkStr1___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Prod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mk", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1;
x_2 = l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2;
x_7 = lean_apply_1(x_1, x_4);
x_8 = lean_apply_1(x_2, x_5);
x_9 = l_Lean_Syntax_mkApp___closed__2;
x_10 = lean_array_push(x_9, x_7);
x_11 = lean_array_push(x_10, x_8);
x_12 = l_Lean_Syntax_mkCApp(x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteProdMkStr1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_instQuoteProdMkStr1___redArg___lam__0), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nil", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1;
x_2 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2;
x_2 = l_Lean_mkCIdent(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cons", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4;
x_2 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5;
lean_inc_ref(x_1);
x_7 = lean_apply_1(x_1, x_4);
x_8 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(x_1, x_5);
x_9 = l_Lean_Syntax_mkApp___closed__2;
x_10 = lean_array_push(x_9, x_7);
x_11 = lean_array_push(x_10, x_8);
x_12 = l_Lean_Syntax_mkCApp(x_6, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___private__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteListMkStr1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instQuoteListMkStr1___private__1), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Array", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkArray", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_7 = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0;
x_8 = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1;
x_9 = l_Nat_reprFast(x_5);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
x_11 = l_Lean_Name_mkStr2(x_7, x_10);
x_12 = l_Lean_Syntax_mkCApp(x_11, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
x_15 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc_ref(x_1);
lean_inc(x_15);
x_16 = lean_apply_1(x_1, x_15);
x_17 = lean_array_push(x_4, x_16);
x_3 = x_14;
x_4 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Meta_Defs_0__Lean_quoteArray_go(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toArray", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0;
x_2 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(8u);
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1;
x_7 = lean_array_to_list(x_2);
x_8 = l___private_Init_Meta_Defs_0__Lean_quoteList___redArg(x_1, x_7);
x_9 = l_Lean_mkOptionalNode___closed__3;
x_10 = lean_array_push(x_9, x_8);
x_11 = l_Lean_Syntax_mkCApp(x_6, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_mkSepArray___closed__0;
x_14 = l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg(x_1, x_2, x_12, x_13);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_quoteArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___private__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instQuoteArrayMkStr1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instQuoteArrayMkStr1___private__1), 3, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Option_hasQuote___redArg___lam__0___closed__1;
x_2 = l_Lean_Option_hasQuote___redArg___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Option_hasQuote___redArg___lam__0___closed__2;
x_2 = lean_mk_syntax_ident(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("some", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Option_hasQuote___redArg___lam__0___closed__4;
x_2 = l_Lean_Option_hasQuote___redArg___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = l_Lean_Option_hasQuote___redArg___lam__0___closed__3;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Option_hasQuote___redArg___lam__0___closed__5;
x_6 = lean_apply_1(x_1, x_4);
x_7 = l_Lean_mkOptionalNode___closed__3;
x_8 = lean_array_push(x_7, x_6);
x_9 = l_Lean_Syntax_mkCApp(x_5, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_hasQuote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_evalPrec___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_expandMacros___lam__0___closed__4;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_evalPrec___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_evalPrec___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected precedence", 21, 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_2, 5);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_8, x_14);
lean_dec(x_8);
lean_ctor_set(x_2, 3, x_15);
lean_inc_ref(x_2);
x_16 = l_Lean_expandMacros(x_1, x_13, x_2, x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Syntax_mkNumLit___closed__1;
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_16);
x_22 = l_Lean_evalPrec___closed__0;
x_23 = l_Lean_Macro_throwErrorAt___redArg(x_18, x_22, x_2, x_19);
lean_dec(x_18);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_2);
x_24 = l_Lean_TSyntax_getNat(x_18);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = l_Lean_Syntax_mkNumLit___closed__1;
lean_inc(x_25);
x_28 = l_Lean_Syntax_isOfKind(x_25, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_evalPrec___closed__0;
x_30 = l_Lean_Macro_throwErrorAt___redArg(x_25, x_29, x_2, x_26);
lean_dec(x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_2);
x_31 = l_Lean_TSyntax_getNat(x_25);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec_ref(x_2);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = l_Lean_expandMacros___closed__0;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get(x_2, 3);
x_44 = lean_ctor_get(x_2, 4);
x_45 = lean_ctor_get(x_2, 5);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_2);
x_46 = lean_nat_dec_eq(x_43, x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_box(x_46);
x_48 = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_43, x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_41);
lean_ctor_set(x_51, 2, x_42);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_44);
lean_ctor_set(x_51, 5, x_45);
lean_inc_ref(x_51);
x_52 = l_Lean_expandMacros(x_1, x_48, x_51, x_3);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = l_Lean_Syntax_mkNumLit___closed__1;
lean_inc(x_53);
x_57 = l_Lean_Syntax_isOfKind(x_53, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
x_58 = l_Lean_evalPrec___closed__0;
x_59 = l_Lean_Macro_throwErrorAt___redArg(x_53, x_58, x_51, x_54);
lean_dec(x_53);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_51);
x_60 = l_Lean_TSyntax_getNat(x_53);
lean_dec(x_53);
if (lean_is_scalar(x_55)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_55;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_54);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_51);
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_64 = x_52;
} else {
 lean_dec_ref(x_52);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
x_66 = l_Lean_expandMacros___closed__0;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
return x_68;
}
}
}
}
static lean_object* _init_l_Lean_evalPrio___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected priority", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_evalPrio(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_2, 5);
x_11 = lean_nat_dec_eq(x_8, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_8, x_14);
lean_dec(x_8);
lean_ctor_set(x_2, 3, x_15);
lean_inc_ref(x_2);
x_16 = l_Lean_expandMacros(x_1, x_13, x_2, x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Syntax_mkNumLit___closed__1;
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_16);
x_22 = l_Lean_evalPrio___closed__0;
x_23 = l_Lean_Macro_throwErrorAt___redArg(x_18, x_22, x_2, x_19);
lean_dec(x_18);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_2);
x_24 = l_Lean_TSyntax_getNat(x_18);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = l_Lean_Syntax_mkNumLit___closed__1;
lean_inc(x_25);
x_28 = l_Lean_Syntax_isOfKind(x_25, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_evalPrio___closed__0;
x_30 = l_Lean_Macro_throwErrorAt___redArg(x_25, x_29, x_2, x_26);
lean_dec(x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_2);
x_31 = l_Lean_TSyntax_getNat(x_25);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec_ref(x_2);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = l_Lean_expandMacros___closed__0;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get(x_2, 3);
x_44 = lean_ctor_get(x_2, 4);
x_45 = lean_ctor_get(x_2, 5);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_2);
x_46 = lean_nat_dec_eq(x_43, x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_box(x_46);
x_48 = lean_alloc_closure((void*)(l_Lean_evalPrec___lam__0___boxed), 2, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_43, x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_41);
lean_ctor_set(x_51, 2, x_42);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_44);
lean_ctor_set(x_51, 5, x_45);
lean_inc_ref(x_51);
x_52 = l_Lean_expandMacros(x_1, x_48, x_51, x_3);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = l_Lean_Syntax_mkNumLit___closed__1;
lean_inc(x_53);
x_57 = l_Lean_Syntax_isOfKind(x_53, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
x_58 = l_Lean_evalPrio___closed__0;
x_59 = l_Lean_Macro_throwErrorAt___redArg(x_53, x_58, x_51, x_54);
lean_dec(x_53);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_51);
x_60 = l_Lean_TSyntax_getNat(x_53);
lean_dec(x_53);
if (lean_is_scalar(x_55)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_55;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_54);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_51);
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_64 = x_52;
} else {
 lean_dec_ref(x_52);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
x_66 = l_Lean_expandMacros___closed__0;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalOptPrio(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_2);
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = l_Lean_evalPrio(x_6, x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_dec(x_7);
x_8 = lean_box(x_1);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_box(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_array_push(x_13, x_3);
x_17 = lean_box(x_15);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_17);
return x_2;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = 0;
x_20 = lean_array_push(x_18, x_3);
x_21 = lean_box(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Array_getSepElems___redArg___lam__0(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_getSepElems___redArg___closed__2;
x_2 = l_Array_getSepElems___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_getSepElems___redArg___closed__6;
x_2 = l_Array_getSepElems___redArg___closed__5;
x_3 = l_Array_getSepElems___redArg___closed__4;
x_4 = l_Array_getSepElems___redArg___closed__3;
x_5 = l_Array_getSepElems___redArg___closed__8;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Array_getSepElems___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_getSepElems___redArg___closed__7;
x_2 = l_Array_getSepElems___redArg___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_getSepElems___redArg___closed__0;
x_4 = lean_array_get_size(x_1);
x_5 = l_Array_getSepElems___redArg___closed__10;
x_6 = lean_nat_dec_lt(x_2, x_4);
if (x_6 == 0)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_box(x_6);
x_8 = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_box(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_nat_dec_le(x_4, x_4);
if (x_11 == 0)
{
if (x_6 == 0)
{
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_3;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_5, x_8, x_1, x_12, x_13, x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
return x_15;
}
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_4);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_5, x_8, x_1, x_16, x_17, x_10);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getSepElems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_getSepElems___redArg___closed__0;
x_5 = lean_array_get_size(x_2);
x_6 = l_Array_getSepElems___redArg___closed__10;
x_7 = lean_nat_dec_lt(x_3, x_5);
if (x_7 == 0)
{
lean_dec_ref(x_2);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_box(x_7);
x_9 = lean_alloc_closure((void*)(l_Array_getSepElems___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_box(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_nat_dec_le(x_5, x_5);
if (x_12 == 0)
{
if (x_7 == 0)
{
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
return x_4;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_9, x_2, x_13, x_14, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_5);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_9, x_2, x_17, x_18, x_11);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_add(x_1, x_16);
x_18 = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(x_2, x_3, x_4, x_17, x_5);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = l_Array_isEmpty___redArg(x_5);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_1, x_20);
if (x_21 == 0)
{
goto block_15;
}
else
{
if (x_19 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_nat_add(x_1, x_22);
x_24 = lean_array_push(x_5, x_6);
x_25 = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(x_2, x_3, x_4, x_23, x_24);
return x_25;
}
else
{
goto block_15;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_add(x_1, x_26);
x_28 = lean_array_push(x_5, x_6);
x_29 = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(x_2, x_3, x_4, x_27, x_28);
return x_29;
}
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_nat_pred(x_1);
x_9 = lean_array_fget_borrowed(x_3, x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_1, x_10);
lean_inc(x_9);
x_12 = lean_array_push(x_5, x_9);
x_13 = lean_array_push(x_12, x_6);
x_14 = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(x_2, x_3, x_4, x_11, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
x_9 = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_array_fget(x_2, x_4);
lean_inc(x_12);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_12);
x_14 = lean_apply_1(x_3, x_12);
x_15 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_mkSepArray___closed__0;
x_6 = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterSepElemsM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_filterSepElems___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_filterSepElems___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_16; uint8_t x_17; 
x_7 = lean_array_fget_borrowed(x_1, x_3);
lean_inc_ref(x_2);
lean_inc(x_7);
x_16 = lean_apply_1(x_2, x_7);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_3 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = l_Array_isEmpty___redArg(x_4);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_3, x_22);
if (x_23 == 0)
{
goto block_15;
}
else
{
if (x_21 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_nat_add(x_3, x_24);
lean_dec(x_3);
lean_inc(x_7);
x_26 = lean_array_push(x_4, x_7);
x_3 = x_25;
x_4 = x_26;
goto _start;
}
else
{
goto block_15;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_add(x_3, x_28);
lean_dec(x_3);
lean_inc(x_7);
x_30 = lean_array_push(x_4, x_7);
x_3 = x_29;
x_4 = x_30;
goto _start;
}
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_nat_pred(x_3);
x_9 = lean_array_fget_borrowed(x_1, x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
lean_inc(x_9);
x_12 = lean_array_push(x_4, x_9);
lean_inc(x_7);
x_13 = lean_array_push(x_12, x_7);
x_3 = x_11;
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_mkSepArray___closed__0;
x_5 = l___private_Init_Meta_Defs_0__Array_filterSepElemsMAux___at___00Array_filterSepElemsM___at___00Array_filterSepElems_spec__0_spec__0(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Array_filterSepElems___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Array_filterSepElemsM___at___00Array_filterSepElems_spec__0(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_filterSepElems___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_filterSepElems(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_fget_borrowed(x_2, x_4);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_mod(x_4, x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
lean_inc(x_11);
x_18 = lean_array_push(x_5, x_11);
x_4 = x_17;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_11);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_3);
x_21 = lean_alloc_closure((void*)(l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_5);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_2);
lean_closure_set(x_21, 4, x_3);
x_22 = lean_apply_1(x_3, x_11);
x_23 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_22, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = lean_array_push(x_2, x_6);
x_10 = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_mkSepArray___closed__0;
x_6 = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mapSepElemsM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_fget_borrowed(x_1, x_3);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_mod(x_3, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
lean_inc(x_7);
x_14 = lean_array_push(x_4, x_7);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc_ref(x_2);
lean_inc(x_7);
x_16 = lean_apply_1(x_2, x_7);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_3, x_17);
lean_dec(x_3);
x_19 = lean_array_push(x_4, x_16);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_mkSepArray___closed__0;
x_5 = l___private_Init_Meta_Defs_0__Array_mapSepElemsMAux___at___00Array_mapSepElemsM___at___00Array_mapSepElems_spec__0_spec__0(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Array_mapSepElems___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Array_mapSepElemsM___at___00Array_mapSepElems_spec__0(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElems___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapSepElems(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_4, 0, x_16);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_5 = x_20;
goto block_9;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_uget(x_1, x_2);
x_25 = lean_array_push(x_22, x_24);
x_26 = lean_box(x_10);
lean_ctor_set(x_4, 1, x_25);
lean_ctor_set(x_4, 0, x_26);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_dec(x_4);
x_28 = lean_array_uget(x_1, x_2);
x_29 = lean_array_push(x_27, x_28);
x_30 = lean_box(x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_5 = x_31;
goto block_9;
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_SepArray_ofElems___closed__0;
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
if (x_5 == 0)
{
lean_dec_ref(x_7);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(x_1, x_9, x_10, x_7);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
return x_12;
}
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(x_1, x_13, x_14, x_7);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_SepArray_getElems___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_SepArray_getElems___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_SepArray_getElems___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_SepArray_getElems(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_SepArray_ofElems___closed__0;
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
if (x_5 == 0)
{
lean_dec_ref(x_7);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(x_1, x_9, x_10, x_7);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
return x_12;
}
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(x_1, x_13, x_14, x_7);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_TSepArray_getElems___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_getElems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_TSepArray_getElems(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___redArg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_mkAtom(x_1);
x_6 = lean_array_push(x_2, x_5);
x_7 = lean_array_push(x_6, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = l_Lean_mkOptionalNode___closed__3;
x_9 = lean_array_push(x_8, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_TSepArray_push___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_TSepArray_push___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_TSepArray_push(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_SepArray_ofElems___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionSepArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_instEmptyCollectionSepArray(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_SepArray_ofElems___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instEmptyCollectionTSepArray___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_instEmptyCollectionTSepArray(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutSepArrayArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_SepArray_getElems___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSepArrayTSyntaxArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_TSepArray_getElems___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Array_getSepElems___redArg___closed__10;
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), x_3, x_1, x_4, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg___lam__1), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_instCoeTSyntaxArrayOfTSyntax(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeOutTSyntaxArrayArray___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_instCoeOutTSyntaxArrayArray(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declId", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1;
x_2 = l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0;
x_3 = l_Lean_expandMacros___lam__0___closed__1;
x_4 = l_Lean_expandMacros___lam__0___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2;
x_3 = lean_box(2);
x_4 = l_Lean_mkOptionalNode___closed__2;
x_5 = l_Lean_Syntax_mkApp___closed__2;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_6, x_4);
x_8 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instCoeTermTSyntaxConsSyntaxNodeKindMkStr4Nil() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 123;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_decodeQuotedChar(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = 123;
x_6 = lean_uint32_dec_eq(x_4, x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_string_utf8_next(x_1, x_2);
x_8 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; uint8_t x_6; uint32_t x_26; uint8_t x_27; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_26 = 34;
x_27 = lean_uint32_dec_eq(x_4, x_26);
if (x_27 == 0)
{
uint32_t x_28; uint8_t x_29; 
x_28 = 123;
x_29 = lean_uint32_dec_eq(x_4, x_28);
x_6 = x_29;
goto block_25;
}
else
{
x_6 = x_27;
goto block_25;
}
block_25:
{
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_1, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 92;
x_9 = lean_uint32_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_push(x_3, x_4);
x_2 = x_5;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar(x_1, x_5);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; 
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unbox_uint32(x_14);
lean_dec(x_14);
x_17 = lean_string_push(x_3, x_16);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_12);
lean_inc_ref(x_1);
x_19 = l_Lean_Syntax_decodeStringGap(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_2 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_22 = lean_box(0);
return x_22;
}
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_23 = lean_box(0);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_3);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_versionString___closed__0;
x_4 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit_loop(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStrLitKind", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrLit(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isInterpolatedStrLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l_Lean_Syntax_getArgs(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_SepArray_ofElems___closed__0;
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_dec_ref(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
if (x_6 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_2);
return x_4;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(x_2, x_10, x_11, x_8);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_SepArray_getElems_spec__0(x_2, x_14, x_15, x_8);
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getSepArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_25; 
x_25 = lean_usize_dec_lt(x_6, x_5);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_array_uget(x_4, x_6);
x_28 = l_Lean_Syntax_isInterpolatedStrLit_x3f(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
x_31 = lean_ctor_get(x_8, 2);
x_32 = lean_ctor_get(x_8, 3);
x_33 = lean_ctor_get(x_8, 4);
x_34 = lean_ctor_get(x_8, 5);
x_35 = l_Lean_replaceRef(x_27, x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_35);
lean_inc_ref(x_2);
x_37 = lean_apply_3(x_2, x_27, x_36, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
lean_inc_ref(x_8);
x_16 = x_7;
x_17 = x_38;
x_18 = x_8;
x_19 = x_39;
goto block_24;
}
else
{
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_37;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
lean_dec_ref(x_28);
lean_inc(x_40);
x_41 = lean_string_isempty(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
x_44 = lean_ctor_get(x_8, 2);
x_45 = lean_ctor_get(x_8, 3);
x_46 = lean_ctor_get(x_8, 4);
x_47 = lean_ctor_get(x_8, 5);
x_48 = l_Lean_replaceRef(x_27, x_47);
lean_dec(x_27);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_44);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set(x_49, 4, x_46);
lean_ctor_set(x_49, 5, x_48);
lean_inc_ref(x_3);
x_50 = lean_apply_3(x_3, x_40, x_49, x_9);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
lean_inc_ref(x_8);
x_16 = x_7;
x_17 = x_51;
x_18 = x_8;
x_19 = x_52;
goto block_24;
}
else
{
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_50;
}
}
else
{
lean_dec(x_40);
lean_dec(x_27);
x_10 = x_7;
x_11 = x_9;
goto block_15;
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_6, x_12);
x_6 = x_13;
x_7 = x_10;
x_9 = x_11;
goto _start;
}
block_24:
{
uint8_t x_20; 
x_20 = l_Lean_Syntax_isMissing(x_16);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc_ref(x_1);
x_21 = lean_apply_4(x_1, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_10 = x_22;
x_11 = x_23;
goto block_15;
}
else
{
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_21;
}
}
else
{
lean_dec_ref(x_18);
lean_dec(x_16);
x_10 = x_17;
x_11 = x_19;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_box(0);
x_8 = lean_array_size(x_1);
x_9 = 0;
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_expandInterpolatedStrChunks_spec__0(x_2, x_3, x_4, x_1, x_8, x_9, x_7, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = l_Lean_Syntax_isMissing(x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_10);
x_14 = l_Lean_versionString___closed__0;
x_15 = lean_apply_3(x_4, x_14, x_5, x_12);
return x_15;
}
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStrChunks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_TSyntax_expandInterpolatedStrChunks(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_++_", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("++", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = 0;
x_7 = l_Lean_SourceInfo_fromRef(x_5, x_6);
x_8 = l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1;
x_9 = l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2;
lean_inc(x_7);
x_10 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Syntax_node3(x_7, x_8, x_1, x_10, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_TSyntax_expandInterpolatedStr___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = 0;
x_7 = l_Lean_SourceInfo_fromRef(x_5, x_6);
x_8 = l_Lean_Syntax_mkApp___closed__1;
x_9 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_7);
x_10 = l_Lean_Syntax_node1(x_7, x_9, x_2);
x_11 = l_Lean_Syntax_node2(x_7, x_8, x_1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_TSyntax_expandInterpolatedStr___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = 0;
x_7 = l_Lean_SourceInfo_fromRef(x_5, x_6);
x_8 = l_Lean_Syntax_mkApp___closed__1;
x_9 = l_Lean_mkOptionalNode___closed__1;
x_10 = lean_box(2);
x_11 = l_Lean_Syntax_mkStrLit(x_2, x_10);
lean_inc(x_7);
x_12 = l_Lean_Syntax_node1(x_7, x_9, x_11);
x_13 = l_Lean_Syntax_node2(x_7, x_8, x_1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_TSyntax_expandInterpolatedStr___lam__2(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__0___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeAscription", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_TSyntax_expandInterpolatedStr___closed__1;
x_2 = l_Lean_expandMacros___lam__0___closed__2;
x_3 = l_Lean_expandMacros___lam__0___closed__1;
x_4 = l_Lean_expandMacros___lam__0___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hygienicLParen", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_TSyntax_expandInterpolatedStr___closed__3;
x_2 = l_Lean_expandMacros___lam__0___closed__2;
x_3 = l_Lean_expandMacros___lam__0___closed__1;
x_4 = l_Lean_expandMacros___lam__0___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TSyntax_expandInterpolatedStr___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_versionString___closed__0;
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("TSyntax", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_TSyntax_expandInterpolatedStr___closed__9;
x_2 = l_Lean_expandMacros___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TSyntax_expandInterpolatedStr___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compat", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_TSyntax_expandInterpolatedStr___closed__12;
x_2 = l_Lean_TSyntax_expandInterpolatedStr___closed__9;
x_3 = l_Lean_expandMacros___lam__0___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TSyntax_expandInterpolatedStr___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_TSyntax_expandInterpolatedStr___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_TSyntax_expandInterpolatedStr___closed__15;
x_2 = l_Lean_TSyntax_expandInterpolatedStr___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_TSyntax_expandInterpolatedStr___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_TSyntax_expandInterpolatedStr___closed__0;
x_8 = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__1___boxed), 4, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_TSyntax_expandInterpolatedStr___lam__2___boxed), 4, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = l_Lean_Syntax_getArgs(x_1);
lean_inc_ref(x_5);
x_11 = l_Lean_TSyntax_expandInterpolatedStrChunks(x_10, x_7, x_8, x_9, x_5, x_6);
lean_dec_ref(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = 0;
x_18 = l_Lean_SourceInfo_fromRef(x_16, x_17);
lean_dec(x_16);
x_19 = l_Lean_TSyntax_expandInterpolatedStr___closed__2;
x_20 = l_Lean_TSyntax_expandInterpolatedStr___closed__4;
x_21 = l_Lean_TSyntax_expandInterpolatedStr___closed__5;
lean_inc(x_18);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_TSyntax_expandInterpolatedStr___closed__7;
x_24 = l_Lean_TSyntax_expandInterpolatedStr___closed__8;
x_25 = lean_box(0);
x_26 = l_Lean_addMacroScope(x_14, x_25, x_15);
x_27 = l_Lean_TSyntax_expandInterpolatedStr___closed__16;
lean_inc(x_18);
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_27);
lean_inc(x_18);
x_29 = l_Lean_Syntax_node1(x_18, x_23, x_28);
lean_inc(x_18);
x_30 = l_Lean_Syntax_node2(x_18, x_20, x_22, x_29);
x_31 = l_Lean_toolchain___closed__0;
lean_inc(x_18);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_18);
x_34 = l_Lean_Syntax_node1(x_18, x_33, x_2);
x_35 = l_Lean_TSyntax_expandInterpolatedStr___closed__17;
lean_inc(x_18);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_18);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Syntax_node5(x_18, x_19, x_30, x_13, x_32, x_34, x_36);
lean_ctor_set(x_11, 0, x_37);
return x_11;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_38 = lean_ctor_get(x_11, 0);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_11);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_5, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_5, 5);
lean_inc(x_42);
lean_dec_ref(x_5);
x_43 = 0;
x_44 = l_Lean_SourceInfo_fromRef(x_42, x_43);
lean_dec(x_42);
x_45 = l_Lean_TSyntax_expandInterpolatedStr___closed__2;
x_46 = l_Lean_TSyntax_expandInterpolatedStr___closed__4;
x_47 = l_Lean_TSyntax_expandInterpolatedStr___closed__5;
lean_inc(x_44);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_TSyntax_expandInterpolatedStr___closed__7;
x_50 = l_Lean_TSyntax_expandInterpolatedStr___closed__8;
x_51 = lean_box(0);
x_52 = l_Lean_addMacroScope(x_40, x_51, x_41);
x_53 = l_Lean_TSyntax_expandInterpolatedStr___closed__16;
lean_inc(x_44);
x_54 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_53);
lean_inc(x_44);
x_55 = l_Lean_Syntax_node1(x_44, x_49, x_54);
lean_inc(x_44);
x_56 = l_Lean_Syntax_node2(x_44, x_46, x_48, x_55);
x_57 = l_Lean_toolchain___closed__0;
lean_inc(x_44);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_44);
x_60 = l_Lean_Syntax_node1(x_44, x_59, x_2);
x_61 = l_Lean_TSyntax_expandInterpolatedStr___closed__17;
lean_inc(x_44);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_44);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Syntax_node5(x_44, x_45, x_56, x_38, x_58, x_60, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_39);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec_ref(x_5);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_11);
if (x_65 == 0)
{
return x_11;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_11, 0);
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_11);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_expandInterpolatedStr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_TSyntax_expandInterpolatedStr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_string_pos_sub(x_6, x_7);
x_9 = lean_string_utf8_extract(x_4, x_5, x_8);
lean_dec(x_8);
lean_dec_ref(x_4);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = l_Lean_versionString___closed__0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getDocString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TSyntax_getDocString(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.TransparencyMode.all", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprTransparencyMode_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.TransparencyMode.default", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprTransparencyMode_repr___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.TransparencyMode.reducible", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprTransparencyMode_repr___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.TransparencyMode.instances", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprTransparencyMode_repr___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.TransparencyMode.none", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprTransparencyMode_repr___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; lean_object* x_24; lean_object* x_31; 
switch (x_1) {
case 0:
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(1024u);
x_39 = lean_nat_dec_le(x_38, x_2);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_3 = x_40;
goto block_9;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_3 = x_41;
goto block_9;
}
}
case 1:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(1024u);
x_43 = lean_nat_dec_le(x_42, x_2);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_10 = x_44;
goto block_16;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_10 = x_45;
goto block_16;
}
}
case 2:
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_unsigned_to_nat(1024u);
x_47 = lean_nat_dec_le(x_46, x_2);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_17 = x_48;
goto block_23;
}
else
{
lean_object* x_49; 
x_49 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_17 = x_49;
goto block_23;
}
}
case 3:
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_unsigned_to_nat(1024u);
x_51 = lean_nat_dec_le(x_50, x_2);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_24 = x_52;
goto block_30;
}
else
{
lean_object* x_53; 
x_53 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_24 = x_53;
goto block_30;
}
}
default: 
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_unsigned_to_nat(1024u);
x_55 = lean_nat_dec_le(x_54, x_2);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_31 = x_56;
goto block_37;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_31 = x_57;
goto block_37;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Meta_instReprTransparencyMode_repr___closed__1;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Meta_instReprTransparencyMode_repr___closed__3;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_Meta_instReprTransparencyMode_repr___closed__5;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
block_30:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lean_Meta_instReprTransparencyMode_repr___closed__7;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_2);
return x_29;
}
block_37:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_Meta_instReprTransparencyMode_repr___closed__9;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = 0;
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = l_Repr_addAppParen(x_35, x_2);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprTransparencyMode_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Meta_instReprTransparencyMode_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instReprTransparencyMode_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprTransparencyMode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReprTransparencyMode___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.EtaStructMode.all", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprEtaStructMode_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.EtaStructMode.notClasses", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprEtaStructMode_repr___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.EtaStructMode.none", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprEtaStructMode_repr___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; 
switch (x_1) {
case 0:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(1024u);
x_25 = lean_nat_dec_le(x_24, x_2);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_3 = x_26;
goto block_9;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_3 = x_27;
goto block_9;
}
}
case 1:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(1024u);
x_29 = lean_nat_dec_le(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_10 = x_30;
goto block_16;
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_10 = x_31;
goto block_16;
}
}
default: 
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_unsigned_to_nat(1024u);
x_33 = lean_nat_dec_le(x_32, x_2);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_Syntax_instReprPreresolved_repr___closed__3;
x_17 = x_34;
goto block_23;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Syntax_instReprPreresolved_repr___closed__4;
x_17 = x_35;
goto block_23;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Meta_instReprEtaStructMode_repr___closed__1;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Meta_instReprEtaStructMode_repr___closed__3;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_Meta_instReprEtaStructMode_repr___closed__5;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprEtaStructMode_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Meta_instReprEtaStructMode_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instReprEtaStructMode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instReprEtaStructMode_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprEtaStructMode() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReprEtaStructMode___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zeta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5;
x_2 = l_Lean_Meta_instReprConfig_repr___redArg___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("beta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eta", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("etaStruct", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("iota", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decide", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("autoUnfold", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failIfUnchanged", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__22;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unfoldPartialApp", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__25;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(20u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zetaDelta", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__28;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("index", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__30;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zetaUnused", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__33;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zetaHave", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__35;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("locals", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig_repr___redArg___closed__38;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_2 = lean_ctor_get_uint8(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, 1);
x_4 = lean_ctor_get_uint8(x_1, 2);
x_5 = lean_ctor_get_uint8(x_1, 3);
x_6 = lean_ctor_get_uint8(x_1, 4);
x_7 = lean_ctor_get_uint8(x_1, 5);
x_8 = lean_ctor_get_uint8(x_1, 6);
x_9 = lean_ctor_get_uint8(x_1, 7);
x_10 = lean_ctor_get_uint8(x_1, 8);
x_11 = lean_ctor_get_uint8(x_1, 9);
x_12 = lean_ctor_get_uint8(x_1, 10);
x_13 = lean_ctor_get_uint8(x_1, 11);
x_14 = lean_ctor_get_uint8(x_1, 12);
x_15 = lean_ctor_get_uint8(x_1, 13);
x_16 = lean_ctor_get_uint8(x_1, 14);
x_17 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5;
x_18 = l_Lean_Meta_instReprConfig_repr___redArg___closed__3;
x_19 = l_Lean_Meta_instReprConfig_repr___redArg___closed__4;
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Bool_repr___redArg(x_2);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = 0;
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4;
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_instReprConfig_repr___redArg___closed__6;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_17);
x_33 = l_Bool_repr___redArg(x_3);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_23);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
x_39 = l_Lean_Meta_instReprConfig_repr___redArg___closed__8;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_17);
x_42 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7;
x_43 = l_Bool_repr___redArg(x_4);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_23);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_26);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_28);
x_49 = l_Lean_Meta_instReprConfig_repr___redArg___closed__10;
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_17);
x_52 = l_Lean_Meta_instReprConfig_repr___redArg___closed__11;
x_53 = l_Lean_Meta_instReprEtaStructMode_repr(x_5, x_20);
x_54 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_23);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_26);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_28);
x_59 = l_Lean_Meta_instReprConfig_repr___redArg___closed__13;
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_17);
x_62 = l_Bool_repr___redArg(x_6);
x_63 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_63, 0, x_19);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_23);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_26);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_28);
x_68 = l_Lean_Meta_instReprConfig_repr___redArg___closed__15;
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_17);
x_71 = l_Bool_repr___redArg(x_7);
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_19);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_23);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_26);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_28);
x_77 = l_Lean_Meta_instReprConfig_repr___redArg___closed__17;
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_17);
x_80 = l_Lean_Meta_instReprConfig_repr___redArg___closed__18;
x_81 = l_Bool_repr___redArg(x_8);
x_82 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_23);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_26);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_28);
x_87 = l_Lean_Meta_instReprConfig_repr___redArg___closed__20;
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_17);
x_90 = l_Lean_Meta_instReprConfig_repr___redArg___closed__21;
x_91 = l_Bool_repr___redArg(x_9);
x_92 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_23);
x_94 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_26);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_28);
x_97 = l_Lean_Meta_instReprConfig_repr___redArg___closed__23;
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_17);
x_100 = l_Lean_Meta_instReprConfig_repr___redArg___closed__24;
x_101 = l_Bool_repr___redArg(x_10);
x_102 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_23);
x_104 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_26);
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_28);
x_107 = l_Lean_Meta_instReprConfig_repr___redArg___closed__26;
x_108 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_17);
x_110 = l_Lean_Meta_instReprConfig_repr___redArg___closed__27;
x_111 = l_Bool_repr___redArg(x_11);
x_112 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_23);
x_114 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_26);
x_116 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_28);
x_117 = l_Lean_Meta_instReprConfig_repr___redArg___closed__29;
x_118 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_17);
x_120 = l_Bool_repr___redArg(x_12);
x_121 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_121, 0, x_52);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_23);
x_123 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_26);
x_125 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_28);
x_126 = l_Lean_Meta_instReprConfig_repr___redArg___closed__31;
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_17);
x_129 = l_Lean_Meta_instReprConfig_repr___redArg___closed__32;
x_130 = l_Bool_repr___redArg(x_13);
x_131 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_23);
x_133 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_26);
x_135 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_28);
x_136 = l_Lean_Meta_instReprConfig_repr___redArg___closed__34;
x_137 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_17);
x_139 = l_Bool_repr___redArg(x_14);
x_140 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_140, 0, x_90);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*1, x_23);
x_142 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_26);
x_144 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_28);
x_145 = l_Lean_Meta_instReprConfig_repr___redArg___closed__36;
x_146 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_17);
x_148 = l_Lean_Meta_instReprConfig_repr___redArg___closed__37;
x_149 = l_Bool_repr___redArg(x_15);
x_150 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set_uint8(x_151, sizeof(void*)*1, x_23);
x_152 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_152, 0, x_147);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_26);
x_154 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_28);
x_155 = l_Lean_Meta_instReprConfig_repr___redArg___closed__39;
x_156 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_17);
x_158 = l_Bool_repr___redArg(x_16);
x_159 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_159, 0, x_80);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_23);
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10;
x_163 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11;
x_164 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
x_165 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12;
x_166 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_23);
return x_168;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_instReprConfig_repr___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_instReprConfig_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_instReprConfig_repr(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instReprConfig_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReprConfig___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxSteps", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5;
x_2 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxDischargeDepth", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(21u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("contextual", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("memoize", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("singlePass", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arith", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimp", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ground", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("implicitDefEqProofs", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(23u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("catchRuntime", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letToHave", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrConsts", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bitVecOfNat", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warnExponents", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(17u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("suggestions", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 4);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 5);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 6);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 7);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 8);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 9);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 10);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 11);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 12);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 13);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 14);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 15);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 16);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 17);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 18);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 19);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 20);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 21);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 22);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 23);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 24);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 25);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 26);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 27);
lean_dec_ref(x_1);
x_32 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5;
x_33 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3;
x_34 = l_Lean_Meta_instReprConfig_repr___redArg___closed__37;
x_35 = l_Nat_reprFast(x_2);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = 0;
x_39 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4;
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(1);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5;
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_32);
x_48 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6;
x_49 = l_Nat_reprFast(x_3);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_38);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_43);
x_56 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8;
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_32);
x_59 = l_Lean_Meta_instReprConfig_repr___redArg___closed__21;
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Bool_repr___redArg(x_4);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_38);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_41);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_43);
x_67 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10;
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_32);
x_70 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11;
x_71 = l_Bool_repr___redArg(x_5);
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_38);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_41);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_43);
x_77 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13;
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_32);
x_80 = l_Bool_repr___redArg(x_6);
x_81 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_81, 0, x_59);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_38);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_41);
x_85 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_43);
x_86 = l_Lean_Meta_instReprConfig_repr___redArg___closed__1;
x_87 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_32);
x_89 = l_Lean_Meta_instReprConfig_repr___redArg___closed__4;
x_90 = l_Bool_repr___redArg(x_7);
x_91 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_38);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_41);
x_95 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_43);
x_96 = l_Lean_Meta_instReprConfig_repr___redArg___closed__6;
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_32);
x_99 = l_Bool_repr___redArg(x_8);
x_100 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_100, 0, x_89);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_38);
x_102 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_41);
x_104 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_43);
x_105 = l_Lean_Meta_instReprConfig_repr___redArg___closed__8;
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_32);
x_108 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7;
x_109 = l_Bool_repr___redArg(x_9);
x_110 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_38);
x_112 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_41);
x_114 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_43);
x_115 = l_Lean_Meta_instReprConfig_repr___redArg___closed__10;
x_116 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_32);
x_118 = l_Lean_Meta_instReprConfig_repr___redArg___closed__11;
x_119 = l_Lean_Meta_instReprEtaStructMode_repr(x_10, x_60);
x_120 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set_uint8(x_121, sizeof(void*)*1, x_38);
x_122 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_41);
x_124 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_43);
x_125 = l_Lean_Meta_instReprConfig_repr___redArg___closed__13;
x_126 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_32);
x_128 = l_Bool_repr___redArg(x_11);
x_129 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_129, 0, x_89);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_38);
x_131 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_41);
x_133 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_43);
x_134 = l_Lean_Meta_instReprConfig_repr___redArg___closed__15;
x_135 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_32);
x_137 = l_Bool_repr___redArg(x_12);
x_138 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_138, 0, x_89);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_38);
x_140 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_41);
x_142 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_43);
x_143 = l_Lean_Meta_instReprConfig_repr___redArg___closed__17;
x_144 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_32);
x_146 = l_Lean_Meta_instReprConfig_repr___redArg___closed__18;
x_147 = l_Bool_repr___redArg(x_13);
x_148 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*1, x_38);
x_150 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_150, 0, x_145);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_41);
x_152 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_43);
x_153 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15;
x_154 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_32);
x_156 = l_Lean_Meta_instReprConfig_repr___redArg___closed__32;
x_157 = l_Bool_repr___redArg(x_14);
x_158 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_38);
x_160 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_160, 0, x_155);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_41);
x_162 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_43);
x_163 = l_Lean_Meta_instReprConfig_repr___redArg___closed__20;
x_164 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_32);
x_166 = l_Bool_repr___redArg(x_15);
x_167 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_167, 0, x_59);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_38);
x_169 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_41);
x_171 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_43);
x_172 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17;
x_173 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_32);
x_175 = l_Bool_repr___redArg(x_16);
x_176 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_176, 0, x_156);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*1, x_38);
x_178 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_41);
x_180 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_43);
x_181 = l_Lean_Meta_instReprConfig_repr___redArg___closed__23;
x_182 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_32);
x_184 = l_Lean_Meta_instReprConfig_repr___redArg___closed__24;
x_185 = l_Bool_repr___redArg(x_17);
x_186 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set_uint8(x_187, sizeof(void*)*1, x_38);
x_188 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_41);
x_190 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_43);
x_191 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19;
x_192 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_32);
x_194 = l_Bool_repr___redArg(x_18);
x_195 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_195, 0, x_146);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_38);
x_197 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_197, 0, x_193);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_41);
x_199 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_43);
x_200 = l_Lean_Meta_instReprConfig_repr___redArg___closed__26;
x_201 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_32);
x_203 = l_Lean_Meta_instReprConfig_repr___redArg___closed__27;
x_204 = l_Bool_repr___redArg(x_19);
x_205 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set_uint8(x_206, sizeof(void*)*1, x_38);
x_207 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_41);
x_209 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_43);
x_210 = l_Lean_Meta_instReprConfig_repr___redArg___closed__29;
x_211 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_32);
x_213 = l_Bool_repr___redArg(x_20);
x_214 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_214, 0, x_118);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*1, x_38);
x_216 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_216, 0, x_212);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_41);
x_218 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_43);
x_219 = l_Lean_Meta_instReprConfig_repr___redArg___closed__31;
x_220 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_32);
x_222 = l_Bool_repr___redArg(x_21);
x_223 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_223, 0, x_156);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set_uint8(x_224, sizeof(void*)*1, x_38);
x_225 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_225, 0, x_221);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_41);
x_227 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_43);
x_228 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21;
x_229 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_32);
x_231 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22;
x_232 = l_Bool_repr___redArg(x_22);
x_233 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*1, x_38);
x_235 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_235, 0, x_230);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_41);
x_237 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_43);
x_238 = l_Lean_Meta_instReprConfig_repr___redArg___closed__34;
x_239 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_32);
x_241 = l_Bool_repr___redArg(x_23);
x_242 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_242, 0, x_59);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set_uint8(x_243, sizeof(void*)*1, x_38);
x_244 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_244, 0, x_240);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_41);
x_246 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_43);
x_247 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24;
x_248 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_32);
x_250 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25;
x_251 = l_Bool_repr___redArg(x_24);
x_252 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set_uint8(x_253, sizeof(void*)*1, x_38);
x_254 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_254, 0, x_249);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_41);
x_256 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_43);
x_257 = l_Lean_Meta_instReprConfig_repr___redArg___closed__36;
x_258 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_32);
x_260 = l_Bool_repr___redArg(x_25);
x_261 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_261, 0, x_34);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set_uint8(x_262, sizeof(void*)*1, x_38);
x_263 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_263, 0, x_259);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_41);
x_265 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_43);
x_266 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27;
x_267 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_32);
x_269 = l_Bool_repr___redArg(x_26);
x_270 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_270, 0, x_118);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set_uint8(x_271, sizeof(void*)*1, x_38);
x_272 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_272, 0, x_268);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_41);
x_274 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_43);
x_275 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29;
x_276 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_32);
x_278 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30;
x_279 = l_Bool_repr___redArg(x_27);
x_280 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set_uint8(x_281, sizeof(void*)*1, x_38);
x_282 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_282, 0, x_277);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_41);
x_284 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_43);
x_285 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32;
x_286 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_32);
x_288 = l_Bool_repr___redArg(x_28);
x_289 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_289, 0, x_278);
lean_ctor_set(x_289, 1, x_288);
x_290 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set_uint8(x_290, sizeof(void*)*1, x_38);
x_291 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_41);
x_293 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_43);
x_294 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34;
x_295 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_32);
x_297 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35;
x_298 = l_Bool_repr___redArg(x_29);
x_299 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set_uint8(x_300, sizeof(void*)*1, x_38);
x_301 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_301, 0, x_296);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_41);
x_303 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_43);
x_304 = l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37;
x_305 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_32);
x_307 = l_Bool_repr___redArg(x_30);
x_308 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_308, 0, x_278);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set_uint8(x_309, sizeof(void*)*1, x_38);
x_310 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_310, 0, x_306);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_41);
x_312 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_43);
x_313 = l_Lean_Meta_instReprConfig_repr___redArg___closed__39;
x_314 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_32);
x_316 = l_Bool_repr___redArg(x_31);
x_317 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_317, 0, x_146);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set_uint8(x_318, sizeof(void*)*1, x_38);
x_319 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10;
x_321 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11;
x_322 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_319);
x_323 = l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12;
x_324 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_325, 0, x_320);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set_uint8(x_326, sizeof(void*)*1, x_38);
return x_326;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_instReprConfig__1_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instReprConfig__1_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_instReprConfig__1_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instReprConfig__1_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprConfig__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReprConfig__1___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(x_2, x_4);
return x_5;
}
default: 
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_List_elem___at___00Lean_Meta_Occurrences_contains_spec__0(x_2, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Occurrences_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Occurrences_isAll(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Occurrences_isAll___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Occurrences_isAll(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_ApplyNewGoals_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_ApplyNewGoals_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_ApplyNewGoals_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_ApplyNewGoals_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Meta_ApplyNewGoals_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Meta_ApplyNewGoals_nonDependentFirst_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Meta_ApplyNewGoals_nonDependentOnly_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_ApplyNewGoals_all_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ApplyNewGoals_all_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_Meta_ApplyNewGoals_all_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_getConfigItems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_getConfigItems___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_getConfigItems___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_getConfigItems___closed__1;
x_2 = l_Lean_Parser_Tactic_getConfigItems___closed__0;
x_3 = l_Lean_expandMacros___lam__0___closed__1;
x_4 = l_Lean_expandMacros___lam__0___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_getConfigItems___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("config", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_getConfigItems___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_getConfigItems___closed__3;
x_2 = l_Lean_Parser_Tactic_getConfigItems___closed__0;
x_3 = l_Lean_expandMacros___lam__0___closed__1;
x_4 = l_Lean_expandMacros___lam__0___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_getConfigItems___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Parser_Tactic_getConfigItems___closed__4;
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_mkSepArray___closed__0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_mkOptionalNode___closed__3;
x_10 = lean_array_push(x_9, x_1);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_SepArray_ofElems___closed__0;
x_17 = lean_array_get_size(x_14);
x_18 = lean_nat_dec_lt(x_15, x_17);
if (x_18 == 0)
{
lean_dec_ref(x_14);
return x_16;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_17, x_17);
if (x_19 == 0)
{
if (x_18 == 0)
{
lean_dec_ref(x_14);
return x_16;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_17);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(x_14, x_20, x_21, x_16);
lean_dec_ref(x_14);
return x_22;
}
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_17);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(x_14, x_23, x_24, x_16);
lean_dec_ref(x_14);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Parser_Tactic_getConfigItems(x_6);
x_8 = l_Array_append___redArg(x_4, x_7);
lean_dec_ref(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_getConfigItems_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mkOptConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Parser_Tactic_getConfigItems___closed__2;
x_3 = lean_box(2);
x_4 = l_Lean_mkOptionalNode___closed__1;
x_5 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_1);
x_6 = l_Lean_Syntax_node1(x_3, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Parser_Tactic_getConfigItems(x_1);
x_4 = l_Lean_Parser_Tactic_getConfigItems(x_2);
x_5 = l_Array_append___redArg(x_3, x_4);
lean_dec_ref(x_4);
x_6 = l_Lean_Parser_Tactic_mkOptConfig(x_5);
return x_6;
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Meta_Defs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_version_major___closed__0 = _init_l_Lean_version_major___closed__0();
lean_mark_persistent(l_Lean_version_major___closed__0);
l_Lean_version_major = _init_l_Lean_version_major();
lean_mark_persistent(l_Lean_version_major);
l_Lean_version_minor___closed__0 = _init_l_Lean_version_minor___closed__0();
lean_mark_persistent(l_Lean_version_minor___closed__0);
l_Lean_version_minor = _init_l_Lean_version_minor();
lean_mark_persistent(l_Lean_version_minor);
l_Lean_version_patch___closed__0 = _init_l_Lean_version_patch___closed__0();
lean_mark_persistent(l_Lean_version_patch___closed__0);
l_Lean_version_patch = _init_l_Lean_version_patch();
lean_mark_persistent(l_Lean_version_patch);
l_Lean_githash___closed__0 = _init_l_Lean_githash___closed__0();
lean_mark_persistent(l_Lean_githash___closed__0);
l_Lean_githash = _init_l_Lean_githash();
lean_mark_persistent(l_Lean_githash);
l_Lean_version_isRelease___closed__0 = _init_l_Lean_version_isRelease___closed__0();
l_Lean_version_isRelease = _init_l_Lean_version_isRelease();
l_Lean_version_specialDesc___closed__0 = _init_l_Lean_version_specialDesc___closed__0();
lean_mark_persistent(l_Lean_version_specialDesc___closed__0);
l_Lean_version_specialDesc = _init_l_Lean_version_specialDesc();
lean_mark_persistent(l_Lean_version_specialDesc);
l_Lean_versionStringCore___closed__0 = _init_l_Lean_versionStringCore___closed__0();
lean_mark_persistent(l_Lean_versionStringCore___closed__0);
l_Lean_versionStringCore___closed__1 = _init_l_Lean_versionStringCore___closed__1();
lean_mark_persistent(l_Lean_versionStringCore___closed__1);
l_Lean_versionStringCore___closed__2 = _init_l_Lean_versionStringCore___closed__2();
lean_mark_persistent(l_Lean_versionStringCore___closed__2);
l_Lean_versionStringCore___closed__3 = _init_l_Lean_versionStringCore___closed__3();
lean_mark_persistent(l_Lean_versionStringCore___closed__3);
l_Lean_versionStringCore___closed__4 = _init_l_Lean_versionStringCore___closed__4();
lean_mark_persistent(l_Lean_versionStringCore___closed__4);
l_Lean_versionStringCore___closed__5 = _init_l_Lean_versionStringCore___closed__5();
lean_mark_persistent(l_Lean_versionStringCore___closed__5);
l_Lean_versionStringCore___closed__6 = _init_l_Lean_versionStringCore___closed__6();
lean_mark_persistent(l_Lean_versionStringCore___closed__6);
l_Lean_versionStringCore___closed__7 = _init_l_Lean_versionStringCore___closed__7();
lean_mark_persistent(l_Lean_versionStringCore___closed__7);
l_Lean_versionStringCore = _init_l_Lean_versionStringCore();
lean_mark_persistent(l_Lean_versionStringCore);
l_Lean_versionString___closed__0 = _init_l_Lean_versionString___closed__0();
lean_mark_persistent(l_Lean_versionString___closed__0);
l_Lean_versionString___closed__1 = _init_l_Lean_versionString___closed__1();
l_Lean_versionString___closed__2 = _init_l_Lean_versionString___closed__2();
lean_mark_persistent(l_Lean_versionString___closed__2);
l_Lean_versionString___closed__3 = _init_l_Lean_versionString___closed__3();
lean_mark_persistent(l_Lean_versionString___closed__3);
l_Lean_versionString___closed__4 = _init_l_Lean_versionString___closed__4();
lean_mark_persistent(l_Lean_versionString___closed__4);
l_Lean_versionString___closed__5 = _init_l_Lean_versionString___closed__5();
lean_mark_persistent(l_Lean_versionString___closed__5);
l_Lean_versionString___closed__6 = _init_l_Lean_versionString___closed__6();
lean_mark_persistent(l_Lean_versionString___closed__6);
l_Lean_versionString___closed__7 = _init_l_Lean_versionString___closed__7();
lean_mark_persistent(l_Lean_versionString___closed__7);
l_Lean_versionString = _init_l_Lean_versionString();
lean_mark_persistent(l_Lean_versionString);
l_Lean_origin___closed__0 = _init_l_Lean_origin___closed__0();
lean_mark_persistent(l_Lean_origin___closed__0);
l_Lean_origin = _init_l_Lean_origin();
lean_mark_persistent(l_Lean_origin);
l_Lean_toolchain___closed__0 = _init_l_Lean_toolchain___closed__0();
lean_mark_persistent(l_Lean_toolchain___closed__0);
l_Lean_toolchain___closed__1 = _init_l_Lean_toolchain___closed__1();
lean_mark_persistent(l_Lean_toolchain___closed__1);
l_Lean_toolchain___closed__2 = _init_l_Lean_toolchain___closed__2();
lean_mark_persistent(l_Lean_toolchain___closed__2);
l_Lean_toolchain___closed__3 = _init_l_Lean_toolchain___closed__3();
lean_mark_persistent(l_Lean_toolchain___closed__3);
l_Lean_toolchain___closed__4 = _init_l_Lean_toolchain___closed__4();
lean_mark_persistent(l_Lean_toolchain___closed__4);
l_Lean_toolchain___closed__5 = _init_l_Lean_toolchain___closed__5();
lean_mark_persistent(l_Lean_toolchain___closed__5);
l_Lean_toolchain = _init_l_Lean_toolchain();
lean_mark_persistent(l_Lean_toolchain);
l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__0();
l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__1();
l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2 = _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__2();
l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3 = _init_l___private_Init_Meta_Defs_0__Lean_isAlphaAscii___closed__3();
l_Lean_isIdFirstAscii___closed__0 = _init_l_Lean_isIdFirstAscii___closed__0();
l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__0();
l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_isAlphanumAscii___closed__1();
l_Lean_isIdRestAscii___closed__0 = _init_l_Lean_isIdRestAscii___closed__0();
l_Lean_isIdRestAscii___closed__1 = _init_l_Lean_isIdRestAscii___closed__1();
l_Lean_isIdRestAscii___closed__2 = _init_l_Lean_isIdRestAscii___closed__2();
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
l_Lean_Name_isInaccessibleUserName___closed__0 = _init_l_Lean_Name_isInaccessibleUserName___closed__0();
lean_mark_persistent(l_Lean_Name_isInaccessibleUserName___closed__0);
l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_needsNoEscape___redArg___closed__0);
l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__0);
l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_escape___closed__1);
l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_escapePart___closed__0);
l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__0);
l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep_maybeEscape___closed__1);
l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__0);
l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithSep___closed__1);
l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__0);
l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__1);
l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2 = _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__2);
l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3 = _init_l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Name_Internal_Meta_toStringWithToken_maybePseudoSyntax___closed__3);
l_Lean_Name_reprPrec___closed__0 = _init_l_Lean_Name_reprPrec___closed__0();
lean_mark_persistent(l_Lean_Name_reprPrec___closed__0);
l_Lean_Name_reprPrec___closed__1 = _init_l_Lean_Name_reprPrec___closed__1();
lean_mark_persistent(l_Lean_Name_reprPrec___closed__1);
l_Lean_Name_reprPrec___closed__2 = _init_l_Lean_Name_reprPrec___closed__2();
lean_mark_persistent(l_Lean_Name_reprPrec___closed__2);
l_Lean_Name_reprPrec___closed__3 = _init_l_Lean_Name_reprPrec___closed__3();
lean_mark_persistent(l_Lean_Name_reprPrec___closed__3);
l_Lean_Name_reprPrec___closed__4 = _init_l_Lean_Name_reprPrec___closed__4();
lean_mark_persistent(l_Lean_Name_reprPrec___closed__4);
l_Lean_Name_reprPrec___closed__5 = _init_l_Lean_Name_reprPrec___closed__5();
lean_mark_persistent(l_Lean_Name_reprPrec___closed__5);
l_Lean_Name_reprPrec___closed__6 = _init_l_Lean_Name_reprPrec___closed__6();
lean_mark_persistent(l_Lean_Name_reprPrec___closed__6);
l_Lean_Name_reprPrec___closed__7 = _init_l_Lean_Name_reprPrec___closed__7();
lean_mark_persistent(l_Lean_Name_reprPrec___closed__7);
l_Lean_Name_reprPrec___closed__8 = _init_l_Lean_Name_reprPrec___closed__8();
lean_mark_persistent(l_Lean_Name_reprPrec___closed__8);
l_Lean_Name_reprPrec___closed__9 = _init_l_Lean_Name_reprPrec___closed__9();
lean_mark_persistent(l_Lean_Name_reprPrec___closed__9);
l_Lean_Name_instRepr___closed__0 = _init_l_Lean_Name_instRepr___closed__0();
lean_mark_persistent(l_Lean_Name_instRepr___closed__0);
l_Lean_Name_instRepr = _init_l_Lean_Name_instRepr();
lean_mark_persistent(l_Lean_Name_instRepr);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__0);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__1);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__2);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__3);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__4);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__5);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__6);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__7);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__8);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__9);
l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10 = _init_l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10();
lean_mark_persistent(l_List_repr_x27___at___00Lean_Syntax_instReprPreresolved_repr_spec__0___redArg___closed__10);
l_Lean_Syntax_instReprPreresolved_repr___closed__0 = _init_l_Lean_Syntax_instReprPreresolved_repr___closed__0();
lean_mark_persistent(l_Lean_Syntax_instReprPreresolved_repr___closed__0);
l_Lean_Syntax_instReprPreresolved_repr___closed__1 = _init_l_Lean_Syntax_instReprPreresolved_repr___closed__1();
lean_mark_persistent(l_Lean_Syntax_instReprPreresolved_repr___closed__1);
l_Lean_Syntax_instReprPreresolved_repr___closed__2 = _init_l_Lean_Syntax_instReprPreresolved_repr___closed__2();
lean_mark_persistent(l_Lean_Syntax_instReprPreresolved_repr___closed__2);
l_Lean_Syntax_instReprPreresolved_repr___closed__3 = _init_l_Lean_Syntax_instReprPreresolved_repr___closed__3();
lean_mark_persistent(l_Lean_Syntax_instReprPreresolved_repr___closed__3);
l_Lean_Syntax_instReprPreresolved_repr___closed__4 = _init_l_Lean_Syntax_instReprPreresolved_repr___closed__4();
lean_mark_persistent(l_Lean_Syntax_instReprPreresolved_repr___closed__4);
l_Lean_Syntax_instReprPreresolved_repr___closed__5 = _init_l_Lean_Syntax_instReprPreresolved_repr___closed__5();
lean_mark_persistent(l_Lean_Syntax_instReprPreresolved_repr___closed__5);
l_Lean_Syntax_instReprPreresolved_repr___closed__6 = _init_l_Lean_Syntax_instReprPreresolved_repr___closed__6();
lean_mark_persistent(l_Lean_Syntax_instReprPreresolved_repr___closed__6);
l_Lean_Syntax_instReprPreresolved_repr___closed__7 = _init_l_Lean_Syntax_instReprPreresolved_repr___closed__7();
lean_mark_persistent(l_Lean_Syntax_instReprPreresolved_repr___closed__7);
l_Lean_Syntax_instReprPreresolved___closed__0 = _init_l_Lean_Syntax_instReprPreresolved___closed__0();
lean_mark_persistent(l_Lean_Syntax_instReprPreresolved___closed__0);
l_Lean_Syntax_instReprPreresolved = _init_l_Lean_Syntax_instReprPreresolved();
lean_mark_persistent(l_Lean_Syntax_instReprPreresolved);
l_Lean_Syntax_instRepr_repr___closed__0 = _init_l_Lean_Syntax_instRepr_repr___closed__0();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__0);
l_Lean_Syntax_instRepr_repr___closed__1 = _init_l_Lean_Syntax_instRepr_repr___closed__1();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__1);
l_Lean_Syntax_instRepr_repr___closed__2 = _init_l_Lean_Syntax_instRepr_repr___closed__2();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__2);
l_Lean_Syntax_instRepr_repr___closed__3 = _init_l_Lean_Syntax_instRepr_repr___closed__3();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__3);
l_Lean_Syntax_instRepr_repr___closed__4 = _init_l_Lean_Syntax_instRepr_repr___closed__4();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__4);
l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0 = _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0();
lean_mark_persistent(l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__0);
l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1 = _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1();
lean_mark_persistent(l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__1);
l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2 = _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2();
lean_mark_persistent(l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__2);
l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3 = _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3();
lean_mark_persistent(l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__3);
l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4 = _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4();
lean_mark_persistent(l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__4);
l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5 = _init_l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5();
lean_mark_persistent(l_Array_Array_repr___at___00Lean_Syntax_instRepr_repr_spec__0___closed__5);
l_Lean_Syntax_instRepr_repr___closed__5 = _init_l_Lean_Syntax_instRepr_repr___closed__5();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__5);
l_Lean_Syntax_instRepr_repr___closed__6 = _init_l_Lean_Syntax_instRepr_repr___closed__6();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__6);
l_Lean_Syntax_instRepr_repr___closed__7 = _init_l_Lean_Syntax_instRepr_repr___closed__7();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__7);
l_Lean_Syntax_instRepr_repr___closed__8 = _init_l_Lean_Syntax_instRepr_repr___closed__8();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__8);
l_Lean_Syntax_instRepr_repr___closed__9 = _init_l_Lean_Syntax_instRepr_repr___closed__9();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__9);
l_Lean_Syntax_instRepr_repr___closed__10 = _init_l_Lean_Syntax_instRepr_repr___closed__10();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__10);
l_Lean_Syntax_instRepr_repr___closed__11 = _init_l_Lean_Syntax_instRepr_repr___closed__11();
lean_mark_persistent(l_Lean_Syntax_instRepr_repr___closed__11);
l_Lean_Syntax_instRepr___closed__0 = _init_l_Lean_Syntax_instRepr___closed__0();
lean_mark_persistent(l_Lean_Syntax_instRepr___closed__0);
l_Lean_Syntax_instRepr = _init_l_Lean_Syntax_instRepr();
lean_mark_persistent(l_Lean_Syntax_instRepr);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__0);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__1);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__2);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__3);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__4);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__5);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__6);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__7);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__8);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__9);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__10);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__11);
l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12 = _init_l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12();
lean_mark_persistent(l_Lean_Syntax_instReprTSyntax_repr___redArg___closed__12);
l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0 = _init_l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0();
lean_mark_persistent(l_Lean_TSyntax_instCoeConsSyntaxNodeKindNil___closed__0);
l_Lean_TSyntax_instCoeIdentTerm___closed__0 = _init_l_Lean_TSyntax_instCoeIdentTerm___closed__0();
lean_mark_persistent(l_Lean_TSyntax_instCoeIdentTerm___closed__0);
l_Lean_TSyntax_instCoeIdentTerm = _init_l_Lean_TSyntax_instCoeIdentTerm();
lean_mark_persistent(l_Lean_TSyntax_instCoeIdentTerm);
l_Lean_TSyntax_instCoeStrLitTerm = _init_l_Lean_TSyntax_instCoeStrLitTerm();
lean_mark_persistent(l_Lean_TSyntax_instCoeStrLitTerm);
l_Lean_TSyntax_instCoeNameLitTerm = _init_l_Lean_TSyntax_instCoeNameLitTerm();
lean_mark_persistent(l_Lean_TSyntax_instCoeNameLitTerm);
l_Lean_TSyntax_instCoeScientificLitTerm = _init_l_Lean_TSyntax_instCoeScientificLitTerm();
lean_mark_persistent(l_Lean_TSyntax_instCoeScientificLitTerm);
l_Lean_TSyntax_instCoeNumLitTerm = _init_l_Lean_TSyntax_instCoeNumLitTerm();
lean_mark_persistent(l_Lean_TSyntax_instCoeNumLitTerm);
l_Lean_TSyntax_instCoeCharLitTerm = _init_l_Lean_TSyntax_instCoeCharLitTerm();
lean_mark_persistent(l_Lean_TSyntax_instCoeCharLitTerm);
l_Lean_TSyntax_instCoeIdentLevel = _init_l_Lean_TSyntax_instCoeIdentLevel();
lean_mark_persistent(l_Lean_TSyntax_instCoeIdentLevel);
l_Lean_TSyntax_instCoeNumLitPrio = _init_l_Lean_TSyntax_instCoeNumLitPrio();
lean_mark_persistent(l_Lean_TSyntax_instCoeNumLitPrio);
l_Lean_TSyntax_instCoeNumLitPrec = _init_l_Lean_TSyntax_instCoeNumLitPrec();
lean_mark_persistent(l_Lean_TSyntax_instCoeNumLitPrec);
l_Lean_Syntax_instBEqPreresolved___closed__0 = _init_l_Lean_Syntax_instBEqPreresolved___closed__0();
lean_mark_persistent(l_Lean_Syntax_instBEqPreresolved___closed__0);
l_Lean_Syntax_instBEqPreresolved = _init_l_Lean_Syntax_instBEqPreresolved();
lean_mark_persistent(l_Lean_Syntax_instBEqPreresolved);
l_Lean_Syntax_instBEq___closed__0 = _init_l_Lean_Syntax_instBEq___closed__0();
lean_mark_persistent(l_Lean_Syntax_instBEq___closed__0);
l_Lean_Syntax_instBEq = _init_l_Lean_Syntax_instBEq();
lean_mark_persistent(l_Lean_Syntax_instBEq);
l_Lean_Syntax_getHead_x3f___closed__0 = _init_l_Lean_Syntax_getHead_x3f___closed__0();
lean_mark_persistent(l_Lean_Syntax_getHead_x3f___closed__0);
l_Lean_expandMacros___lam__0___closed__0 = _init_l_Lean_expandMacros___lam__0___closed__0();
lean_mark_persistent(l_Lean_expandMacros___lam__0___closed__0);
l_Lean_expandMacros___lam__0___closed__1 = _init_l_Lean_expandMacros___lam__0___closed__1();
lean_mark_persistent(l_Lean_expandMacros___lam__0___closed__1);
l_Lean_expandMacros___lam__0___closed__2 = _init_l_Lean_expandMacros___lam__0___closed__2();
lean_mark_persistent(l_Lean_expandMacros___lam__0___closed__2);
l_Lean_expandMacros___lam__0___closed__3 = _init_l_Lean_expandMacros___lam__0___closed__3();
lean_mark_persistent(l_Lean_expandMacros___lam__0___closed__3);
l_Lean_expandMacros___lam__0___closed__4 = _init_l_Lean_expandMacros___lam__0___closed__4();
lean_mark_persistent(l_Lean_expandMacros___lam__0___closed__4);
l_Lean_expandMacros___closed__0 = _init_l_Lean_expandMacros___closed__0();
lean_mark_persistent(l_Lean_expandMacros___closed__0);
l_Lean_mkCIdentFrom___closed__0 = _init_l_Lean_mkCIdentFrom___closed__0();
lean_mark_persistent(l_Lean_mkCIdentFrom___closed__0);
l_Lean_mkCIdentFrom___closed__1 = _init_l_Lean_mkCIdentFrom___closed__1();
lean_mark_persistent(l_Lean_mkCIdentFrom___closed__1);
l_Lean_mkGroupNode___closed__0 = _init_l_Lean_mkGroupNode___closed__0();
lean_mark_persistent(l_Lean_mkGroupNode___closed__0);
l_Lean_mkGroupNode___closed__1 = _init_l_Lean_mkGroupNode___closed__1();
lean_mark_persistent(l_Lean_mkGroupNode___closed__1);
l_Lean_mkSepArray___closed__0 = _init_l_Lean_mkSepArray___closed__0();
lean_mark_persistent(l_Lean_mkSepArray___closed__0);
l_Lean_mkSepArray___closed__1 = _init_l_Lean_mkSepArray___closed__1();
lean_mark_persistent(l_Lean_mkSepArray___closed__1);
l_Lean_mkOptionalNode___closed__0 = _init_l_Lean_mkOptionalNode___closed__0();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__0);
l_Lean_mkOptionalNode___closed__1 = _init_l_Lean_mkOptionalNode___closed__1();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__1);
l_Lean_mkOptionalNode___closed__2 = _init_l_Lean_mkOptionalNode___closed__2();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__2);
l_Lean_mkOptionalNode___closed__3 = _init_l_Lean_mkOptionalNode___closed__3();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__3);
l_Lean_mkHole___closed__0 = _init_l_Lean_mkHole___closed__0();
lean_mark_persistent(l_Lean_mkHole___closed__0);
l_Lean_mkHole___closed__1 = _init_l_Lean_mkHole___closed__1();
lean_mark_persistent(l_Lean_mkHole___closed__1);
l_Lean_Syntax_SepArray_ofElems___closed__0 = _init_l_Lean_Syntax_SepArray_ofElems___closed__0();
lean_mark_persistent(l_Lean_Syntax_SepArray_ofElems___closed__0);
l_Lean_Syntax_SepArray_ofElems___closed__1 = _init_l_Lean_Syntax_SepArray_ofElems___closed__1();
lean_mark_persistent(l_Lean_Syntax_SepArray_ofElems___closed__1);
l_Lean_Syntax_mkApp___closed__0 = _init_l_Lean_Syntax_mkApp___closed__0();
lean_mark_persistent(l_Lean_Syntax_mkApp___closed__0);
l_Lean_Syntax_mkApp___closed__1 = _init_l_Lean_Syntax_mkApp___closed__1();
lean_mark_persistent(l_Lean_Syntax_mkApp___closed__1);
l_Lean_Syntax_mkApp___closed__2 = _init_l_Lean_Syntax_mkApp___closed__2();
lean_mark_persistent(l_Lean_Syntax_mkApp___closed__2);
l_Lean_Syntax_mkCharLit___closed__0 = _init_l_Lean_Syntax_mkCharLit___closed__0();
lean_mark_persistent(l_Lean_Syntax_mkCharLit___closed__0);
l_Lean_Syntax_mkCharLit___closed__1 = _init_l_Lean_Syntax_mkCharLit___closed__1();
lean_mark_persistent(l_Lean_Syntax_mkCharLit___closed__1);
l_Lean_Syntax_mkStrLit___closed__0 = _init_l_Lean_Syntax_mkStrLit___closed__0();
lean_mark_persistent(l_Lean_Syntax_mkStrLit___closed__0);
l_Lean_Syntax_mkStrLit___closed__1 = _init_l_Lean_Syntax_mkStrLit___closed__1();
lean_mark_persistent(l_Lean_Syntax_mkStrLit___closed__1);
l_Lean_Syntax_mkNumLit___closed__0 = _init_l_Lean_Syntax_mkNumLit___closed__0();
lean_mark_persistent(l_Lean_Syntax_mkNumLit___closed__0);
l_Lean_Syntax_mkNumLit___closed__1 = _init_l_Lean_Syntax_mkNumLit___closed__1();
lean_mark_persistent(l_Lean_Syntax_mkNumLit___closed__1);
l_Lean_Syntax_mkScientificLit___closed__0 = _init_l_Lean_Syntax_mkScientificLit___closed__0();
lean_mark_persistent(l_Lean_Syntax_mkScientificLit___closed__0);
l_Lean_Syntax_mkScientificLit___closed__1 = _init_l_Lean_Syntax_mkScientificLit___closed__1();
lean_mark_persistent(l_Lean_Syntax_mkScientificLit___closed__1);
l_Lean_Syntax_mkNameLit___closed__0 = _init_l_Lean_Syntax_mkNameLit___closed__0();
lean_mark_persistent(l_Lean_Syntax_mkNameLit___closed__0);
l_Lean_Syntax_mkNameLit___closed__1 = _init_l_Lean_Syntax_mkNameLit___closed__1();
lean_mark_persistent(l_Lean_Syntax_mkNameLit___closed__1);
l_Lean_Syntax_decodeNatLitVal_x3f___closed__0 = _init_l_Lean_Syntax_decodeNatLitVal_x3f___closed__0();
lean_mark_persistent(l_Lean_Syntax_decodeNatLitVal_x3f___closed__0);
l_Lean_Syntax_isFieldIdx_x3f___closed__0 = _init_l_Lean_Syntax_isFieldIdx_x3f___closed__0();
lean_mark_persistent(l_Lean_Syntax_isFieldIdx_x3f___closed__0);
l_Lean_Syntax_isFieldIdx_x3f___closed__1 = _init_l_Lean_Syntax_isFieldIdx_x3f___closed__1();
lean_mark_persistent(l_Lean_Syntax_isFieldIdx_x3f___closed__1);
l_Lean_Syntax_decodeQuotedChar___boxed__const__1 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__1();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__1);
l_Lean_Syntax_decodeQuotedChar___boxed__const__2 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__2();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__2);
l_Lean_Syntax_decodeQuotedChar___boxed__const__3 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__3();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__3);
l_Lean_Syntax_decodeQuotedChar___boxed__const__4 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__4();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__4);
l_Lean_Syntax_decodeQuotedChar___boxed__const__5 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__5();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__5);
l_Lean_Syntax_decodeQuotedChar___boxed__const__6 = _init_l_Lean_Syntax_decodeQuotedChar___boxed__const__6();
lean_mark_persistent(l_Lean_Syntax_decodeQuotedChar___boxed__const__6);
l_Lean_Syntax_decodeStringGap___closed__0 = _init_l_Lean_Syntax_decodeStringGap___closed__0();
lean_mark_persistent(l_Lean_Syntax_decodeStringGap___closed__0);
l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__0);
l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_splitNameLitAux___closed__1);
l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0 = _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0();
lean_mark_persistent(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__0);
l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1 = _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1();
lean_mark_persistent(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__1);
l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2 = _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2();
lean_mark_persistent(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__2);
l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3 = _init_l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3();
lean_mark_persistent(l_List_foldr___at___00Substring_Raw_toName_spec__0___closed__3);
l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__0);
l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_TSyntax_isHexNum_x3f___closed__1);
l_Lean_TSyntax_getScientific___closed__0 = _init_l_Lean_TSyntax_getScientific___closed__0();
lean_mark_persistent(l_Lean_TSyntax_getScientific___closed__0);
l_Lean_TSyntax_getScientific___closed__1 = _init_l_Lean_TSyntax_getScientific___closed__1();
lean_mark_persistent(l_Lean_TSyntax_getScientific___closed__1);
l_Lean_instQuoteTermMkStr1___closed__0 = _init_l_Lean_instQuoteTermMkStr1___closed__0();
lean_mark_persistent(l_Lean_instQuoteTermMkStr1___closed__0);
l_Lean_instQuoteTermMkStr1 = _init_l_Lean_instQuoteTermMkStr1();
lean_mark_persistent(l_Lean_instQuoteTermMkStr1);
l_Lean_instQuoteBoolMkStr1___lam__0___closed__0 = _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__0();
lean_mark_persistent(l_Lean_instQuoteBoolMkStr1___lam__0___closed__0);
l_Lean_instQuoteBoolMkStr1___lam__0___closed__1 = _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__1();
lean_mark_persistent(l_Lean_instQuoteBoolMkStr1___lam__0___closed__1);
l_Lean_instQuoteBoolMkStr1___lam__0___closed__2 = _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__2();
lean_mark_persistent(l_Lean_instQuoteBoolMkStr1___lam__0___closed__2);
l_Lean_instQuoteBoolMkStr1___lam__0___closed__3 = _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__3();
lean_mark_persistent(l_Lean_instQuoteBoolMkStr1___lam__0___closed__3);
l_Lean_instQuoteBoolMkStr1___lam__0___closed__4 = _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__4();
lean_mark_persistent(l_Lean_instQuoteBoolMkStr1___lam__0___closed__4);
l_Lean_instQuoteBoolMkStr1___lam__0___closed__5 = _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__5();
lean_mark_persistent(l_Lean_instQuoteBoolMkStr1___lam__0___closed__5);
l_Lean_instQuoteBoolMkStr1___lam__0___closed__6 = _init_l_Lean_instQuoteBoolMkStr1___lam__0___closed__6();
lean_mark_persistent(l_Lean_instQuoteBoolMkStr1___lam__0___closed__6);
l_Lean_instQuoteBoolMkStr1___closed__0 = _init_l_Lean_instQuoteBoolMkStr1___closed__0();
lean_mark_persistent(l_Lean_instQuoteBoolMkStr1___closed__0);
l_Lean_instQuoteBoolMkStr1 = _init_l_Lean_instQuoteBoolMkStr1();
lean_mark_persistent(l_Lean_instQuoteBoolMkStr1);
l_Lean_instQuoteCharCharLitKind___closed__0 = _init_l_Lean_instQuoteCharCharLitKind___closed__0();
lean_mark_persistent(l_Lean_instQuoteCharCharLitKind___closed__0);
l_Lean_instQuoteCharCharLitKind = _init_l_Lean_instQuoteCharCharLitKind();
lean_mark_persistent(l_Lean_instQuoteCharCharLitKind);
l_Lean_instQuoteStringStrLitKind___closed__0 = _init_l_Lean_instQuoteStringStrLitKind___closed__0();
lean_mark_persistent(l_Lean_instQuoteStringStrLitKind___closed__0);
l_Lean_instQuoteStringStrLitKind = _init_l_Lean_instQuoteStringStrLitKind();
lean_mark_persistent(l_Lean_instQuoteStringStrLitKind);
l_Lean_instQuoteNatNumLitKind___closed__0 = _init_l_Lean_instQuoteNatNumLitKind___closed__0();
lean_mark_persistent(l_Lean_instQuoteNatNumLitKind___closed__0);
l_Lean_instQuoteNatNumLitKind = _init_l_Lean_instQuoteNatNumLitKind();
lean_mark_persistent(l_Lean_instQuoteNatNumLitKind);
l_Lean_instQuoteRawMkStr1___lam__0___closed__0 = _init_l_Lean_instQuoteRawMkStr1___lam__0___closed__0();
lean_mark_persistent(l_Lean_instQuoteRawMkStr1___lam__0___closed__0);
l_Lean_instQuoteRawMkStr1___lam__0___closed__1 = _init_l_Lean_instQuoteRawMkStr1___lam__0___closed__1();
lean_mark_persistent(l_Lean_instQuoteRawMkStr1___lam__0___closed__1);
l_Lean_instQuoteRawMkStr1___lam__0___closed__2 = _init_l_Lean_instQuoteRawMkStr1___lam__0___closed__2();
lean_mark_persistent(l_Lean_instQuoteRawMkStr1___lam__0___closed__2);
l_Lean_instQuoteRawMkStr1___closed__0 = _init_l_Lean_instQuoteRawMkStr1___closed__0();
lean_mark_persistent(l_Lean_instQuoteRawMkStr1___closed__0);
l_Lean_instQuoteRawMkStr1 = _init_l_Lean_instQuoteRawMkStr1();
lean_mark_persistent(l_Lean_instQuoteRawMkStr1);
l_Lean_quoteNameMk___closed__0 = _init_l_Lean_quoteNameMk___closed__0();
lean_mark_persistent(l_Lean_quoteNameMk___closed__0);
l_Lean_quoteNameMk___closed__1 = _init_l_Lean_quoteNameMk___closed__1();
lean_mark_persistent(l_Lean_quoteNameMk___closed__1);
l_Lean_quoteNameMk___closed__2 = _init_l_Lean_quoteNameMk___closed__2();
lean_mark_persistent(l_Lean_quoteNameMk___closed__2);
l_Lean_quoteNameMk___closed__3 = _init_l_Lean_quoteNameMk___closed__3();
lean_mark_persistent(l_Lean_quoteNameMk___closed__3);
l_Lean_quoteNameMk___closed__4 = _init_l_Lean_quoteNameMk___closed__4();
lean_mark_persistent(l_Lean_quoteNameMk___closed__4);
l_Lean_quoteNameMk___closed__5 = _init_l_Lean_quoteNameMk___closed__5();
lean_mark_persistent(l_Lean_quoteNameMk___closed__5);
l_Lean_quoteNameMk___closed__6 = _init_l_Lean_quoteNameMk___closed__6();
lean_mark_persistent(l_Lean_quoteNameMk___closed__6);
l_Lean_quoteNameMk___closed__7 = _init_l_Lean_quoteNameMk___closed__7();
lean_mark_persistent(l_Lean_quoteNameMk___closed__7);
l_Lean_instQuoteNameMkStr1___private__1___closed__0 = _init_l_Lean_instQuoteNameMkStr1___private__1___closed__0();
lean_mark_persistent(l_Lean_instQuoteNameMkStr1___private__1___closed__0);
l_Lean_instQuoteNameMkStr1___private__1___closed__1 = _init_l_Lean_instQuoteNameMkStr1___private__1___closed__1();
lean_mark_persistent(l_Lean_instQuoteNameMkStr1___private__1___closed__1);
l_Lean_instQuoteNameMkStr1___closed__0 = _init_l_Lean_instQuoteNameMkStr1___closed__0();
lean_mark_persistent(l_Lean_instQuoteNameMkStr1___closed__0);
l_Lean_instQuoteNameMkStr1 = _init_l_Lean_instQuoteNameMkStr1();
lean_mark_persistent(l_Lean_instQuoteNameMkStr1);
l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0 = _init_l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__0);
l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1 = _init_l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__1);
l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2 = _init_l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_instQuoteProdMkStr1___redArg___lam__0___closed__2);
l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__0);
l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__1);
l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2 = _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__2);
l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3 = _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__3);
l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4 = _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__4);
l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5 = _init_l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_quoteList___redArg___closed__5);
l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__0);
l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_quoteArray_go___redArg___closed__1);
l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0 = _init_l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__0);
l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1 = _init_l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_quoteArray___redArg___closed__1);
l_Lean_Option_hasQuote___redArg___lam__0___closed__0 = _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Option_hasQuote___redArg___lam__0___closed__0);
l_Lean_Option_hasQuote___redArg___lam__0___closed__1 = _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Option_hasQuote___redArg___lam__0___closed__1);
l_Lean_Option_hasQuote___redArg___lam__0___closed__2 = _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_Option_hasQuote___redArg___lam__0___closed__2);
l_Lean_Option_hasQuote___redArg___lam__0___closed__3 = _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_Option_hasQuote___redArg___lam__0___closed__3);
l_Lean_Option_hasQuote___redArg___lam__0___closed__4 = _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__4();
lean_mark_persistent(l_Lean_Option_hasQuote___redArg___lam__0___closed__4);
l_Lean_Option_hasQuote___redArg___lam__0___closed__5 = _init_l_Lean_Option_hasQuote___redArg___lam__0___closed__5();
lean_mark_persistent(l_Lean_Option_hasQuote___redArg___lam__0___closed__5);
l_Lean_evalPrec___closed__0 = _init_l_Lean_evalPrec___closed__0();
lean_mark_persistent(l_Lean_evalPrec___closed__0);
l_Lean_evalPrio___closed__0 = _init_l_Lean_evalPrio___closed__0();
lean_mark_persistent(l_Lean_evalPrio___closed__0);
l_Array_getSepElems___redArg___closed__0 = _init_l_Array_getSepElems___redArg___closed__0();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__0);
l_Array_getSepElems___redArg___closed__1 = _init_l_Array_getSepElems___redArg___closed__1();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__1);
l_Array_getSepElems___redArg___closed__2 = _init_l_Array_getSepElems___redArg___closed__2();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__2);
l_Array_getSepElems___redArg___closed__3 = _init_l_Array_getSepElems___redArg___closed__3();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__3);
l_Array_getSepElems___redArg___closed__4 = _init_l_Array_getSepElems___redArg___closed__4();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__4);
l_Array_getSepElems___redArg___closed__5 = _init_l_Array_getSepElems___redArg___closed__5();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__5);
l_Array_getSepElems___redArg___closed__6 = _init_l_Array_getSepElems___redArg___closed__6();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__6);
l_Array_getSepElems___redArg___closed__7 = _init_l_Array_getSepElems___redArg___closed__7();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__7);
l_Array_getSepElems___redArg___closed__8 = _init_l_Array_getSepElems___redArg___closed__8();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__8);
l_Array_getSepElems___redArg___closed__9 = _init_l_Array_getSepElems___redArg___closed__9();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__9);
l_Array_getSepElems___redArg___closed__10 = _init_l_Array_getSepElems___redArg___closed__10();
lean_mark_persistent(l_Array_getSepElems___redArg___closed__10);
l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0 = _init_l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0();
lean_mark_persistent(l_Lean_Syntax_instCoeOutTSyntaxArrayArray___closed__0);
l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0 = _init_l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0();
lean_mark_persistent(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__0);
l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1 = _init_l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1();
lean_mark_persistent(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__1);
l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2 = _init_l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2();
lean_mark_persistent(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___lam__0___closed__2);
l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0 = _init_l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0();
lean_mark_persistent(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil___closed__0);
l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil = _init_l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil();
lean_mark_persistent(l_Lean_Syntax_instCoeIdentTSyntaxConsSyntaxNodeKindMkStr4Nil);
l_Lean_Syntax_instCoeTermTSyntaxConsSyntaxNodeKindMkStr4Nil = _init_l_Lean_Syntax_instCoeTermTSyntaxConsSyntaxNodeKindMkStr4Nil();
lean_mark_persistent(l_Lean_Syntax_instCoeTermTSyntaxConsSyntaxNodeKindMkStr4Nil);
l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1 = _init_l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1();
lean_mark_persistent(l___private_Init_Meta_Defs_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1);
l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0 = _init_l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0();
lean_mark_persistent(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__0);
l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1 = _init_l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1();
lean_mark_persistent(l_Lean_Syntax_isInterpolatedStrLit_x3f___closed__1);
l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0 = _init_l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__0);
l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1 = _init_l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__1);
l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2 = _init_l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___lam__0___closed__2);
l_Lean_TSyntax_expandInterpolatedStr___closed__0 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__0();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__0);
l_Lean_TSyntax_expandInterpolatedStr___closed__1 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__1();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__1);
l_Lean_TSyntax_expandInterpolatedStr___closed__2 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__2();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__2);
l_Lean_TSyntax_expandInterpolatedStr___closed__3 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__3();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__3);
l_Lean_TSyntax_expandInterpolatedStr___closed__4 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__4();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__4);
l_Lean_TSyntax_expandInterpolatedStr___closed__5 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__5();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__5);
l_Lean_TSyntax_expandInterpolatedStr___closed__6 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__6();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__6);
l_Lean_TSyntax_expandInterpolatedStr___closed__7 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__7();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__7);
l_Lean_TSyntax_expandInterpolatedStr___closed__8 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__8();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__8);
l_Lean_TSyntax_expandInterpolatedStr___closed__9 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__9();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__9);
l_Lean_TSyntax_expandInterpolatedStr___closed__10 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__10();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__10);
l_Lean_TSyntax_expandInterpolatedStr___closed__11 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__11();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__11);
l_Lean_TSyntax_expandInterpolatedStr___closed__12 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__12();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__12);
l_Lean_TSyntax_expandInterpolatedStr___closed__13 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__13();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__13);
l_Lean_TSyntax_expandInterpolatedStr___closed__14 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__14();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__14);
l_Lean_TSyntax_expandInterpolatedStr___closed__15 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__15();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__15);
l_Lean_TSyntax_expandInterpolatedStr___closed__16 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__16();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__16);
l_Lean_TSyntax_expandInterpolatedStr___closed__17 = _init_l_Lean_TSyntax_expandInterpolatedStr___closed__17();
lean_mark_persistent(l_Lean_TSyntax_expandInterpolatedStr___closed__17);
l_Lean_Meta_instReprTransparencyMode_repr___closed__0 = _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__0();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode_repr___closed__0);
l_Lean_Meta_instReprTransparencyMode_repr___closed__1 = _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__1();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode_repr___closed__1);
l_Lean_Meta_instReprTransparencyMode_repr___closed__2 = _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__2();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode_repr___closed__2);
l_Lean_Meta_instReprTransparencyMode_repr___closed__3 = _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__3();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode_repr___closed__3);
l_Lean_Meta_instReprTransparencyMode_repr___closed__4 = _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__4();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode_repr___closed__4);
l_Lean_Meta_instReprTransparencyMode_repr___closed__5 = _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__5();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode_repr___closed__5);
l_Lean_Meta_instReprTransparencyMode_repr___closed__6 = _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__6();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode_repr___closed__6);
l_Lean_Meta_instReprTransparencyMode_repr___closed__7 = _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__7();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode_repr___closed__7);
l_Lean_Meta_instReprTransparencyMode_repr___closed__8 = _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__8();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode_repr___closed__8);
l_Lean_Meta_instReprTransparencyMode_repr___closed__9 = _init_l_Lean_Meta_instReprTransparencyMode_repr___closed__9();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode_repr___closed__9);
l_Lean_Meta_instReprTransparencyMode___closed__0 = _init_l_Lean_Meta_instReprTransparencyMode___closed__0();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode___closed__0);
l_Lean_Meta_instReprTransparencyMode = _init_l_Lean_Meta_instReprTransparencyMode();
lean_mark_persistent(l_Lean_Meta_instReprTransparencyMode);
l_Lean_Meta_instReprEtaStructMode_repr___closed__0 = _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__0();
lean_mark_persistent(l_Lean_Meta_instReprEtaStructMode_repr___closed__0);
l_Lean_Meta_instReprEtaStructMode_repr___closed__1 = _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__1();
lean_mark_persistent(l_Lean_Meta_instReprEtaStructMode_repr___closed__1);
l_Lean_Meta_instReprEtaStructMode_repr___closed__2 = _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__2();
lean_mark_persistent(l_Lean_Meta_instReprEtaStructMode_repr___closed__2);
l_Lean_Meta_instReprEtaStructMode_repr___closed__3 = _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__3();
lean_mark_persistent(l_Lean_Meta_instReprEtaStructMode_repr___closed__3);
l_Lean_Meta_instReprEtaStructMode_repr___closed__4 = _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__4();
lean_mark_persistent(l_Lean_Meta_instReprEtaStructMode_repr___closed__4);
l_Lean_Meta_instReprEtaStructMode_repr___closed__5 = _init_l_Lean_Meta_instReprEtaStructMode_repr___closed__5();
lean_mark_persistent(l_Lean_Meta_instReprEtaStructMode_repr___closed__5);
l_Lean_Meta_instReprEtaStructMode___closed__0 = _init_l_Lean_Meta_instReprEtaStructMode___closed__0();
lean_mark_persistent(l_Lean_Meta_instReprEtaStructMode___closed__0);
l_Lean_Meta_instReprEtaStructMode = _init_l_Lean_Meta_instReprEtaStructMode();
lean_mark_persistent(l_Lean_Meta_instReprEtaStructMode);
l_Lean_Meta_instReprConfig_repr___redArg___closed__0 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__0);
l_Lean_Meta_instReprConfig_repr___redArg___closed__1 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__1);
l_Lean_Meta_instReprConfig_repr___redArg___closed__2 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__2);
l_Lean_Meta_instReprConfig_repr___redArg___closed__3 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__3);
l_Lean_Meta_instReprConfig_repr___redArg___closed__4 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__4);
l_Lean_Meta_instReprConfig_repr___redArg___closed__5 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__5);
l_Lean_Meta_instReprConfig_repr___redArg___closed__6 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__6);
l_Lean_Meta_instReprConfig_repr___redArg___closed__7 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__7);
l_Lean_Meta_instReprConfig_repr___redArg___closed__8 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__8);
l_Lean_Meta_instReprConfig_repr___redArg___closed__9 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__9);
l_Lean_Meta_instReprConfig_repr___redArg___closed__10 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__10);
l_Lean_Meta_instReprConfig_repr___redArg___closed__11 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__11);
l_Lean_Meta_instReprConfig_repr___redArg___closed__12 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__12);
l_Lean_Meta_instReprConfig_repr___redArg___closed__13 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__13();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__13);
l_Lean_Meta_instReprConfig_repr___redArg___closed__14 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__14();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__14);
l_Lean_Meta_instReprConfig_repr___redArg___closed__15 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__15();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__15);
l_Lean_Meta_instReprConfig_repr___redArg___closed__16 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__16();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__16);
l_Lean_Meta_instReprConfig_repr___redArg___closed__17 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__17();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__17);
l_Lean_Meta_instReprConfig_repr___redArg___closed__18 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__18();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__18);
l_Lean_Meta_instReprConfig_repr___redArg___closed__19 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__19();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__19);
l_Lean_Meta_instReprConfig_repr___redArg___closed__20 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__20();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__20);
l_Lean_Meta_instReprConfig_repr___redArg___closed__21 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__21();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__21);
l_Lean_Meta_instReprConfig_repr___redArg___closed__22 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__22();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__22);
l_Lean_Meta_instReprConfig_repr___redArg___closed__23 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__23();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__23);
l_Lean_Meta_instReprConfig_repr___redArg___closed__24 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__24();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__24);
l_Lean_Meta_instReprConfig_repr___redArg___closed__25 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__25();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__25);
l_Lean_Meta_instReprConfig_repr___redArg___closed__26 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__26();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__26);
l_Lean_Meta_instReprConfig_repr___redArg___closed__27 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__27();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__27);
l_Lean_Meta_instReprConfig_repr___redArg___closed__28 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__28();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__28);
l_Lean_Meta_instReprConfig_repr___redArg___closed__29 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__29();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__29);
l_Lean_Meta_instReprConfig_repr___redArg___closed__30 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__30();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__30);
l_Lean_Meta_instReprConfig_repr___redArg___closed__31 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__31();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__31);
l_Lean_Meta_instReprConfig_repr___redArg___closed__32 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__32();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__32);
l_Lean_Meta_instReprConfig_repr___redArg___closed__33 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__33();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__33);
l_Lean_Meta_instReprConfig_repr___redArg___closed__34 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__34();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__34);
l_Lean_Meta_instReprConfig_repr___redArg___closed__35 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__35();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__35);
l_Lean_Meta_instReprConfig_repr___redArg___closed__36 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__36();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__36);
l_Lean_Meta_instReprConfig_repr___redArg___closed__37 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__37();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__37);
l_Lean_Meta_instReprConfig_repr___redArg___closed__38 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__38();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__38);
l_Lean_Meta_instReprConfig_repr___redArg___closed__39 = _init_l_Lean_Meta_instReprConfig_repr___redArg___closed__39();
lean_mark_persistent(l_Lean_Meta_instReprConfig_repr___redArg___closed__39);
l_Lean_Meta_instReprConfig___closed__0 = _init_l_Lean_Meta_instReprConfig___closed__0();
lean_mark_persistent(l_Lean_Meta_instReprConfig___closed__0);
l_Lean_Meta_instReprConfig = _init_l_Lean_Meta_instReprConfig();
lean_mark_persistent(l_Lean_Meta_instReprConfig);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__0);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__1);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__2);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__3);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__4);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__5);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__6);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__7);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__8);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__9);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__10);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__11);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__12);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__13);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__14);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__15);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__16);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__17);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__18);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__19);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__20);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__21);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__22);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__23);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__24);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__25);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__26);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__27);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__28);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__29);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__30);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__31);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__32);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__33);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__34);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__35);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__36);
l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37 = _init_l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1_repr___redArg___closed__37);
l_Lean_Meta_instReprConfig__1___closed__0 = _init_l_Lean_Meta_instReprConfig__1___closed__0();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1___closed__0);
l_Lean_Meta_instReprConfig__1 = _init_l_Lean_Meta_instReprConfig__1();
lean_mark_persistent(l_Lean_Meta_instReprConfig__1);
l_Lean_Parser_Tactic_getConfigItems___closed__1 = _init_l_Lean_Parser_Tactic_getConfigItems___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_getConfigItems___closed__1);
l_Lean_Parser_Tactic_getConfigItems___closed__0 = _init_l_Lean_Parser_Tactic_getConfigItems___closed__0();
lean_mark_persistent(l_Lean_Parser_Tactic_getConfigItems___closed__0);
l_Lean_Parser_Tactic_getConfigItems___closed__2 = _init_l_Lean_Parser_Tactic_getConfigItems___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_getConfigItems___closed__2);
l_Lean_Parser_Tactic_getConfigItems___closed__3 = _init_l_Lean_Parser_Tactic_getConfigItems___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_getConfigItems___closed__3);
l_Lean_Parser_Tactic_getConfigItems___closed__4 = _init_l_Lean_Parser_Tactic_getConfigItems___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_getConfigItems___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
