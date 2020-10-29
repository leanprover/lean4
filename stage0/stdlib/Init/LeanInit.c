// Lean compiler output
// Module: Init.LeanInit
// Imports: Init.Data.Option.BasicAux Init.Data.String.Basic Init.Data.Array.Basic Init.Data.Array.ForIn Init.Data.UInt Init.Data.Hashable Init.Control.Reader Init.Control.EState Init.Control.StateRef Init.Control.Option
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
lean_object* l_Array_getSepElems___rarg___boxed(lean_object*);
lean_object* l_Lean_Syntax_identToAtom_match__1(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_simpMacroScopesAux_match__1(lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__4;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f___boxed(lean_object*);
lean_object* l_Lean_mkAppStx(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__6___rarg(lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_extractImported_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_isNameLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar_match__1(lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__7;
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeOctalLitAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___at_Lean_Syntax_getHeadInfo___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_nullKind;
lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__11;
lean_object* l_Lean_Macro_throwUnsupported___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__17___closed__3;
lean_object* l_Lean_identKind___closed__1;
lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__2___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint32_t l_Lean_idBeginEscape;
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption(lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux_match__1(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__2;
lean_object* l_Lean_Init_LeanInit___instance__9;
lean_object* l_Lean_Syntax_getKind_match__1(lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__2___closed__1;
lean_object* l_Array_filterSepElemsM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_capitalize(lean_object*);
lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
lean_object* l_Lean_monadNameGeneratorLift(lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_hasArgs_match__1(lean_object*);
lean_object* l_Lean_mkSepArray_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat___boxed(lean_object*);
lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Init_LeanInit_0__Lean_quoteName___closed__6;
lean_object* l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__10___closed__1;
lean_object* l_Lean_Syntax_identToAtom_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_extractMainModule___closed__2;
lean_object* l_Lean_Syntax_getKind_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__1;
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__3(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_extractImported___closed__2;
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___boxed(lean_object*);
lean_object* l_Lean_Syntax_isOfKind___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___at_Lean_Syntax_findAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fieldIdxKind___closed__1;
lean_object* l_Lean_Macro_mkMacroEnvSimple;
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
lean_object* l_Lean_charLitKind___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_isGreek___boxed(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_Init_LeanInit___instance__4___closed__1;
uint32_t l_Lean_idEndEscape;
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__5;
lean_object* l_Lean_isIdRest___boxed(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
uint8_t l_Lean_isIdBeginEscape(uint32_t);
lean_object* l_Lean_Syntax_isLit_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_withFreshMacroScope(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption_match__1(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_extractImported___closed__1;
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5;
lean_object* l_Lean_mkNameSimple(lean_object*);
lean_object* l_Lean_isIdFirst___boxed(lean_object*);
lean_object* l_Lean_mkHole___boxed(lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__19___rarg___closed__4;
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_charLitKind___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_expandMacros___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_interpolatedStrKind;
lean_object* l_Lean_Macro_withIncRecDepth___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_expandMacroNotAvailable_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__19___rarg___closed__3;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_getEvenElems___rarg___closed__1;
lean_object* l_Lean_Syntax_strLitToAtom_match__1(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__4;
lean_object* l_Lean_Name_beq_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_extractMacroScopesAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_extractMacroScopesAux_match__1(lean_object*);
lean_object* l_Lean_Syntax_identToStrLit(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit___boxed(lean_object*);
lean_object* l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Macro_Context_currRecDepth___default;
lean_object* l___private_Init_LeanInit_0__Lean_quoteName___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAppStx___closed__4;
lean_object* l_Lean_NameGenerator_namePrefix___default;
lean_object* l_Array_filterSepElems___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__2;
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__2;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_nameLitKind;
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__1;
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop_match__1(lean_object*);
lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Init_LeanInit_0__Lean_extractMainModule___closed__1;
lean_object* l_Lean_maxRecDepthErrorMessage___closed__1;
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__6;
lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object*);
lean_object* l_Array_mapSepElems(lean_object*, lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__13(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_interpolatedStrLitKind___closed__2;
lean_object* l_Lean_Syntax_getKind___closed__2;
lean_object* l_Lean_Syntax_getKind___closed__1;
lean_object* l_Lean_Name_capitalize_match__1(lean_object*);
lean_object* l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isAtom_match__1(lean_object*);
lean_object* l_Lean_expandMacros___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___closed__3;
lean_object* l_Array_findSomeMAux___at_Lean_Syntax_findAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom(lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__13___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal(lean_object*);
lean_object* l_Lean_Macro_mkMacroEnv___boxed(lean_object*);
lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__5;
lean_object* l_Lean_mkStxNumLit(lean_object*, lean_object*);
lean_object* l_Array_mapSepElems___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepStx___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_hasMacroScopes_match__1(lean_object*);
lean_object* l_Lean_Name_Init_LeanInit___instance__4;
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdent_match__1(lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Macro_MacroEnvPointed;
lean_object* l_Lean_Name_appendAfter_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__20___rarg(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter___closed__1;
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_interpolatedStrLitKind___closed__1;
lean_object* l_Array_iterateMAux___at_Lean_Syntax_getSepArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_numLitKind;
lean_object* l_Lean_choiceKind___closed__1;
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_expandMacroNotAvailable_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Macro_mkMacroEnvSimple___closed__1;
lean_object* l___private_Init_LeanInit_0__Lean_quoteName___closed__7;
lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_mkFreshId___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_identToStrLit_match__1(lean_object*);
lean_object* l_Lean_strLitKind;
lean_object* l_Lean_Syntax_decodeCharLit_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Macro_expandMacro_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__3(lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f_match__1(lean_object*);
lean_object* l_Array_getSepElems(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_monadNameGeneratorLift___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Init_Data_Repr___instance__9___rarg___closed__1;
lean_object* l_Lean_Init_LeanInit___instance__19___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId___boxed(lean_object*);
lean_object* l_Lean_Syntax_hasArgs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__1;
lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__2;
lean_object* l_Lean_Syntax_isStrLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_capitalize_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__1(lean_object*);
lean_object* l_Lean_Macro_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*);
lean_object* l_Lean_Name_hash_match__1(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__4;
lean_object* l_Lean_expandMacros_match__1(lean_object*);
lean_object* l_Lean_firstFrontendMacroScope___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___rarg(lean_object*, lean_object*);
lean_object* l_String_capitalize(lean_object*);
lean_object* l_Lean_numLitKind___closed__1;
lean_object* l_Lean_NameGenerator_next(lean_object*);
lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object*);
lean_object* l_Lean_strLitKind___closed__1;
lean_object* l_Lean_Syntax_isNatLitAux___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteName___closed__3;
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__6;
lean_object* l_Lean_Name_appendAfter_match__1(lean_object*);
lean_object* l_Lean_Syntax_getArgs___boxed(lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Array_getSepElems___rarg(lean_object*);
lean_object* l_Lean_reservedMacroScope;
lean_object* l_Lean_Macro_throwError(lean_object*);
lean_object* l_Lean_NameGenerator_namePrefix___default___closed__1;
lean_object* l_Lean_mkNullNode(lean_object*);
lean_object* l_Lean_Syntax_getArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadQuotation_addMacroScope___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_strLitKind___closed__2;
lean_object* l___private_Init_LeanInit_0__Lean_quoteName_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteName___closed__5;
lean_object* l___private_Init_LeanInit_0__Lean_quoteName___closed__8;
lean_object* l_Lean_Macro_expandMacro_x3f___rarg(lean_object*);
lean_object* l_Lean_Macro_expandMacroNotAvailable_x3f___closed__1;
lean_object* l_Lean_Init_LeanInit___instance__17(lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__19_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f_match__1(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Array_umapMAux___at_Lean_expandMacros___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_strLitToAtom_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_choiceKind;
lean_object* l_Lean_charLitKind;
lean_object* l_Lean_Macro_mkMacroEnv(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_extractMainModule_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_idx___default;
lean_object* l_Lean_mkFreshId(lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_mkOptionalNode_match__1(lean_object*);
lean_object* l_Lean_numLitKind___closed__2;
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux_match__1(lean_object*);
lean_object* l_Lean_Syntax_isNameLit_x3f_match__1(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__2(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f_match__1(lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__19___rarg___closed__2;
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_findAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Name_Init_LeanInit___instance__3___closed__1;
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit___boxed(lean_object*, lean_object*);
lean_object* l_Nat_pred(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_match__1(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter_match__1(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteList(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit(lean_object*);
lean_object* l_Lean_interpolatedStrKind___closed__2;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Name_hash_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__19(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__1;
lean_object* l_Lean_Syntax_isNone_match__1(lean_object*);
lean_object* l_Array_filterSepElemsM(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l___private_Init_LeanInit_0__Lean_quoteList_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__18;
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_Init_LeanInit___instance__5;
lean_object* l_Lean_Name_appendBefore_match__1(lean_object*);
lean_object* l_Array_iterateMAux___at_Array_getSepElems___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_Init_LeanInit___instance__6;
lean_object* l_Lean_Syntax_setKind_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_mkChild(lean_object*);
lean_object* l_Lean_mkSepArray_match__2(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__6;
lean_object* l___private_Init_LeanInit_0__Lean_extractMainModule_match__1(lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeBinLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId_match__1___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_assembleParts(lean_object*, lean_object*);
lean_object* l_Lean_nullKind___closed__1;
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
lean_object* l_Lean_SourceInfo_pos___default;
lean_object* l_Lean_Syntax_getOptionalIdent_x3f_match__1(lean_object*);
lean_object* l_Lean_Syntax_decodeStrLit___boxed(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameGenerator_namePrefix___default___closed__2;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isIdEndEscape(uint32_t);
lean_object* l___private_Init_LeanInit_0__Lean_quoteName_match__1(lean_object*);
lean_object* l_Lean_Syntax_getArgs_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeCharLit(lean_object*);
lean_object* l_Lean_SourceInfo_leading___default;
lean_object* l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__2;
uint8_t l_Char_isAlpha(uint32_t);
lean_object* l___private_Init_LeanInit_0__Lean_assembleParts_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_hasQuote(lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
lean_object* l_Lean_Syntax_isToken_match__1(lean_object*);
lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_mkSepStx(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__18___closed__1;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__14;
lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_Macro_Init_LeanInit___instance__13___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isLetterLike___boxed(lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
lean_object* l_Lean_Syntax_isAtom_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f_match__1(lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__19___rarg___closed__1;
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__2;
lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__3;
lean_object* l_Lean_identKind;
lean_object* l_Lean_Name_beq_match__1(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__5;
extern lean_object* l_Option_get_x21___rarg___closed__4;
lean_object* l_Lean_Syntax_isLit_x3f_match__2(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__6(lean_object*);
lean_object* l_Lean_Syntax_setKind_match__1(lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__13___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_mkMacroEnvImp(lean_object*);
lean_object* l_Lean_Macro_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__8;
lean_object* l_Lean_Name_appendAfter(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_Syntax_getArg_match__1(lean_object*);
extern lean_object* l_String_splitAux___closed__1;
lean_object* l_Lean_Init_LeanInit___instance__16(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_extractImported(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdent_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__12;
lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__7;
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks___closed__1;
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_simpMacroScopesAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
lean_object* l_Lean_mkStxStrLit___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_withIncRecDepth(lean_object*);
lean_object* l_Lean_Name_append_match__1(lean_object*);
lean_object* l_String_quote(lean_object*);
uint8_t l_Char_isAlphanum(uint32_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_isGreek(uint32_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg___boxed(lean_object*, lean_object*);
lean_object* l_Array_filterSepElems(lean_object*, lean_object*);
lean_object* l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_identToAtom(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendBefore_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_assembleParts_match__1(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___boxed(lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__8___closed__1;
lean_object* l_Lean_mkSepArray_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray_match__1(lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___rarg(lean_object*);
lean_object* l_Lean_Syntax_decodeCharLit_match__1(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___closed__1;
lean_object* l_Lean_NameGenerator_curr(lean_object*);
lean_object* l_Lean_Syntax_getId_match__1(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_extractImported_match__1(lean_object*);
lean_object* l_Lean_Syntax_isToken_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_isCharLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__3;
lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Name_hasMacroScopes___boxed(lean_object*);
lean_object* l_Lean_MonadQuotation_addMacroScope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isIdBeginEscape___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux(lean_object*);
lean_object* l_Lean_Name_hasMacroScopes___closed__1;
lean_object* l_Lean_Macro_mkMacroEnvSimple___closed__2;
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__10;
lean_object* l_Lean_Name_append_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__4;
lean_object* l_Array_findSomeMAux___at_Lean_Syntax_getHeadInfo___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__1;
lean_object* l_Lean_Name_Init_LeanInit___instance__5___closed__1;
lean_object* l_Array_iterateMAux___at_Array_getSepElems___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCAppStx(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__2(lean_object*);
lean_object* l_Array_iterateMAux___at_Array_getSepElems___spec__1(lean_object*);
lean_object* l_List_foldl___at_Lean_MacroScopesView_review___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Init_LeanInit_0__Lean_quoteName___closed__1;
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Name_hasMacroScopes_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__15(lean_object*);
lean_object* l_Lean_expandMacros_match__2(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__21___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__21___rarg___closed__1;
lean_object* l_Lean_NameGenerator_Init_LeanInit___instance__6___closed__1;
lean_object* l_Lean_Syntax_isStrLit_x3f_match__1(lean_object*);
lean_object* l_Lean_Syntax_decodeNameLit(lean_object*);
lean_object* l_Lean_Name_toStringWithSep_match__1(lean_object*);
lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object*);
lean_object* l_Lean_Macro_expandMacro_x3fImp(lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_isIdEndEscape___boxed(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteList_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux_match__1(lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux_match__1(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___closed__1;
lean_object* l_Lean_Syntax_decodeStrLit(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteName___closed__9;
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isIdFirst(uint32_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_findAux_match__1(lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* l_Lean_Syntax_isNone___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_isToken___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_mkCIdentFrom___closed__1;
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed__const__3;
lean_object* l___private_Init_LeanInit_0__Lean_extractMacroScopesAux(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_identToStrLit_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteName___closed__4;
lean_object* l_Lean_Init_LeanInit___instance__19_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_quoteName(lean_object*);
lean_object* l_Lean_Syntax_decodeNameLit___boxed(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Name_Init_LeanInit___instance__3;
lean_object* l_Lean_expandMacros_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__21___rarg___closed__2;
lean_object* l_Lean_nameLitKind___closed__2;
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat_match__1(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_assembleParts___closed__2;
lean_object* l_Lean_Macro_throwUnsupported(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_mkStxLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_toNat(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___closed__2;
lean_object* l_Lean_Name_appendBefore(lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Syntax_getOp___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f___boxed(lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__1(lean_object*);
lean_object* l_Lean_Macro_withIncRecDepth___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom___closed__2;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_interpolatedStrKind___closed__1;
lean_object* l___private_Init_LeanInit_0__Lean_extractMainModule(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__21(lean_object*);
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___closed__4;
lean_object* lean_simp_macro_scopes(lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_Syntax_getSepArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Init_Core___instance__1___closed__1;
lean_object* l___private_Init_LeanInit_0__Lean_assembleParts___closed__1;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Syntax_strLitToAtom___boxed(lean_object*);
lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeStrLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_simpMacroScopesAux(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_mkAtomFrom___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__1;
lean_object* l_Lean_Syntax_decodeNatLitVal___boxed(lean_object*);
lean_object* l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_monadNameGeneratorLift___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal___closed__1;
lean_object* l_Lean_Init_LeanInit___instance__7___closed__1;
lean_object* l_Lean_Syntax_decodeQuotedChar_match__5(lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__17___closed__4;
lean_object* l_Lean_mkSepArray___closed__1;
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__4(lean_object*);
lean_object* l_Lean_mkSepArray___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MonadQuotation_addMacroScope(lean_object*);
lean_object* l_Lean_Syntax_isNone_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeQuotedChar_match__5___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_Syntax_findAux(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___boxed(lean_object*);
lean_object* l_Lean_defaultMaxRecDepth;
lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOp(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1;
lean_object* l_Lean_Syntax_getOptional_x3f_match__1(lean_object*);
uint8_t l_Lean_Syntax_isToken(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__17___closed__1;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeDecimalLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l_Lean_MonadQuotation_addMacroScope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__17___boxed(lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_string_hash(lean_object*);
lean_object* l_Lean_Option_hasQuote___rarg(lean_object*);
lean_object* l_Lean_SourceInfo_trailing___default;
lean_object* l_Lean_interpolatedStrLitKind;
lean_object* l_Lean_Name_append___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux(lean_object*);
lean_object* l_Lean_Macro_Context_maxRecDepth___default;
lean_object* l_Lean_Init_LeanInit___instance__21___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isIdRest(uint32_t);
lean_object* l_Lean_Syntax_isIdent___boxed(lean_object*);
lean_object* l_Lean_expandMacros_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__17___closed__2;
lean_object* l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_nameLitKind___closed__1;
lean_object* l_Lean_Syntax_isNatLitAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__15___boxed(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Init_LeanInit___instance__20(lean_object*);
uint8_t l_Lean_isGreek(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 913;
x_3 = x_2 <= x_1;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint32_t x_5; uint8_t x_6; 
x_5 = 989;
x_6 = x_1 <= x_5;
return x_6;
}
}
}
lean_object* l_Lean_isGreek___boxed(lean_object* x_1) {
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
uint8_t l_Lean_isLetterLike(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; uint32_t x_4; uint8_t x_5; uint32_t x_6; uint8_t x_7; uint32_t x_8; uint8_t x_9; uint32_t x_10; uint8_t x_11; uint32_t x_12; uint8_t x_13; uint32_t x_14; uint8_t x_15; uint32_t x_16; uint8_t x_17; uint32_t x_18; uint8_t x_19; uint32_t x_20; uint8_t x_21; uint32_t x_22; uint8_t x_23; uint32_t x_24; uint8_t x_25; uint32_t x_26; uint8_t x_27; uint32_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_41; uint8_t x_52; uint8_t x_63; 
x_2 = 945;
x_3 = x_2 <= x_1;
x_4 = 969;
x_5 = x_1 <= x_4;
x_6 = 955;
x_7 = x_1 == x_6;
x_8 = 913;
x_9 = x_8 <= x_1;
x_10 = 937;
x_11 = x_1 <= x_10;
x_12 = 928;
x_13 = x_1 == x_12;
x_14 = 931;
x_15 = x_1 == x_14;
x_16 = 970;
x_17 = x_16 <= x_1;
x_18 = 1019;
x_19 = x_1 <= x_18;
x_20 = 7936;
x_21 = x_20 <= x_1;
x_22 = 8190;
x_23 = x_1 <= x_22;
x_24 = 8448;
x_25 = x_24 <= x_1;
x_26 = 8527;
x_27 = x_1 <= x_26;
x_28 = 119964;
x_29 = x_28 <= x_1;
if (x_3 == 0)
{
uint8_t x_86; 
x_86 = 0;
x_63 = x_86;
goto block_85;
}
else
{
if (x_7 == 0)
{
if (x_5 == 0)
{
uint8_t x_87; 
x_87 = 0;
x_63 = x_87;
goto block_85;
}
else
{
uint8_t x_88; 
x_88 = 1;
x_63 = x_88;
goto block_85;
}
}
else
{
uint8_t x_89; 
x_89 = 0;
x_63 = x_89;
goto block_85;
}
}
block_40:
{
if (x_30 == 0)
{
if (x_25 == 0)
{
if (x_23 == 0)
{
if (x_29 == 0)
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
else
{
uint32_t x_32; uint8_t x_33; 
x_32 = 120223;
x_33 = x_1 <= x_32;
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = 1;
return x_34;
}
}
else
{
if (x_23 == 0)
{
if (x_29 == 0)
{
return x_27;
}
else
{
if (x_27 == 0)
{
uint32_t x_35; uint8_t x_36; 
x_35 = 120223;
x_36 = x_1 <= x_35;
return x_36;
}
else
{
uint8_t x_37; 
x_37 = 1;
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = 1;
return x_38;
}
}
}
else
{
uint8_t x_39; 
x_39 = 1;
return x_39;
}
}
block_51:
{
if (x_41 == 0)
{
if (x_21 == 0)
{
if (x_25 == 0)
{
if (x_29 == 0)
{
uint8_t x_42; 
x_42 = 0;
return x_42;
}
else
{
uint32_t x_43; uint8_t x_44; 
x_43 = 120223;
x_44 = x_1 <= x_43;
return x_44;
}
}
else
{
if (x_29 == 0)
{
return x_27;
}
else
{
if (x_27 == 0)
{
uint32_t x_45; uint8_t x_46; 
x_45 = 120223;
x_46 = x_1 <= x_45;
return x_46;
}
else
{
uint8_t x_47; 
x_47 = 1;
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
x_48 = 0;
x_30 = x_48;
goto block_40;
}
}
else
{
if (x_21 == 0)
{
uint8_t x_49; 
x_49 = 1;
return x_49;
}
else
{
uint8_t x_50; 
x_50 = 1;
x_30 = x_50;
goto block_40;
}
}
}
block_62:
{
if (x_52 == 0)
{
if (x_21 == 0)
{
if (x_19 == 0)
{
if (x_25 == 0)
{
if (x_29 == 0)
{
uint8_t x_53; 
x_53 = 0;
return x_53;
}
else
{
uint32_t x_54; uint8_t x_55; 
x_54 = 120223;
x_55 = x_1 <= x_54;
return x_55;
}
}
else
{
if (x_29 == 0)
{
return x_27;
}
else
{
if (x_27 == 0)
{
uint32_t x_56; uint8_t x_57; 
x_56 = 120223;
x_57 = x_1 <= x_56;
return x_57;
}
else
{
uint8_t x_58; 
x_58 = 1;
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
x_59 = 1;
return x_59;
}
}
else
{
x_30 = x_19;
goto block_40;
}
}
else
{
if (x_21 == 0)
{
uint8_t x_60; 
x_60 = 1;
return x_60;
}
else
{
uint8_t x_61; 
x_61 = 1;
x_30 = x_61;
goto block_40;
}
}
}
block_85:
{
uint8_t x_64; 
if (x_9 == 0)
{
uint8_t x_84; 
x_84 = 0;
x_64 = x_84;
goto block_83;
}
else
{
x_64 = x_11;
goto block_83;
}
block_83:
{
uint8_t x_65; 
if (x_13 == 0)
{
uint8_t x_81; 
x_81 = 1;
x_65 = x_81;
goto block_80;
}
else
{
uint8_t x_82; 
x_82 = 0;
x_65 = x_82;
goto block_80;
}
block_80:
{
if (x_64 == 0)
{
if (x_63 == 0)
{
if (x_17 == 0)
{
uint8_t x_66; 
x_66 = 0;
x_41 = x_66;
goto block_51;
}
else
{
uint8_t x_67; 
x_67 = 0;
x_52 = x_67;
goto block_62;
}
}
else
{
if (x_17 == 0)
{
uint8_t x_68; 
x_68 = 1;
x_41 = x_68;
goto block_51;
}
else
{
uint8_t x_69; 
x_69 = 1;
x_52 = x_69;
goto block_62;
}
}
}
else
{
if (x_15 == 0)
{
if (x_65 == 0)
{
if (x_63 == 0)
{
if (x_17 == 0)
{
uint8_t x_70; 
x_70 = 0;
x_41 = x_70;
goto block_51;
}
else
{
uint8_t x_71; 
x_71 = 0;
x_52 = x_71;
goto block_62;
}
}
else
{
if (x_17 == 0)
{
uint8_t x_72; 
x_72 = 1;
x_41 = x_72;
goto block_51;
}
else
{
uint8_t x_73; 
x_73 = 1;
x_52 = x_73;
goto block_62;
}
}
}
else
{
if (x_17 == 0)
{
uint8_t x_74; 
x_74 = 1;
x_41 = x_74;
goto block_51;
}
else
{
uint8_t x_75; 
x_75 = 1;
x_52 = x_75;
goto block_62;
}
}
}
else
{
if (x_63 == 0)
{
if (x_17 == 0)
{
uint8_t x_76; 
x_76 = 0;
x_41 = x_76;
goto block_51;
}
else
{
uint8_t x_77; 
x_77 = 0;
x_52 = x_77;
goto block_62;
}
}
else
{
if (x_17 == 0)
{
uint8_t x_78; 
x_78 = 1;
x_41 = x_78;
goto block_51;
}
else
{
uint8_t x_79; 
x_79 = 1;
x_52 = x_79;
goto block_62;
}
}
}
}
}
}
}
}
}
lean_object* l_Lean_isLetterLike___boxed(lean_object* x_1) {
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
uint8_t l_Lean_isSubScriptAlnum(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; uint32_t x_4; uint8_t x_5; uint32_t x_6; uint8_t x_7; uint32_t x_8; uint8_t x_9; uint32_t x_10; uint8_t x_11; 
x_2 = 8320;
x_3 = x_2 <= x_1;
x_4 = 8329;
x_5 = x_1 <= x_4;
x_6 = 8336;
x_7 = x_6 <= x_1;
x_8 = 8348;
x_9 = x_1 <= x_8;
x_10 = 7522;
x_11 = x_10 <= x_1;
if (x_3 == 0)
{
if (x_7 == 0)
{
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 7530;
x_14 = x_1 <= x_13;
return x_14;
}
}
else
{
if (x_11 == 0)
{
return x_9;
}
else
{
if (x_9 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 7530;
x_16 = x_1 <= x_15;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
}
}
else
{
if (x_7 == 0)
{
if (x_5 == 0)
{
if (x_11 == 0)
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
else
{
uint32_t x_19; uint8_t x_20; 
x_19 = 7530;
x_20 = x_1 <= x_19;
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
}
else
{
if (x_5 == 0)
{
if (x_11 == 0)
{
return x_9;
}
else
{
if (x_9 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 7530;
x_23 = x_1 <= x_22;
return x_23;
}
else
{
uint8_t x_24; 
x_24 = 1;
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
}
}
}
lean_object* l_Lean_isSubScriptAlnum___boxed(lean_object* x_1) {
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
uint8_t l_Lean_isIdFirst(uint32_t x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; uint8_t x_4; 
x_2 = l_Char_isAlpha(x_1);
x_3 = 95;
x_4 = x_1 == x_3;
if (x_4 == 0)
{
if (x_2 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_isLetterLike(x_1);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_isIdFirst___boxed(lean_object* x_1) {
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
uint8_t l_Lean_isIdRest(uint32_t x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; uint8_t x_4; 
x_2 = l_Char_isAlphanum(x_1);
x_3 = 95;
x_4 = x_1 == x_3;
if (x_4 == 0)
{
if (x_2 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 39;
x_6 = x_1 == x_5;
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 33;
x_8 = x_1 == x_7;
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 63;
x_10 = x_1 == x_9;
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = l_Lean_isLetterLike(x_1);
x_12 = l_Lean_isSubScriptAlnum(x_1);
if (x_11 == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
}
lean_object* l_Lean_isIdRest___boxed(lean_object* x_1) {
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
uint8_t l_Lean_isIdBeginEscape(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = l_Lean_idBeginEscape;
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_Lean_isIdBeginEscape___boxed(lean_object* x_1) {
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
uint8_t l_Lean_isIdEndEscape(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = l_Lean_idEndEscape;
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_Lean_isIdEndEscape___boxed(lean_object* x_1) {
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
static lean_object* _init_l_Lean_Init_LeanInit___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Name_hash_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_3(x_3, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_3(x_4, x_12, x_13, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Name_hash_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_hash_match__1___rarg), 4, 0);
return x_2;
}
}
size_t l_Lean_Name_hash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
size_t x_2; 
x_2 = 1723;
return x_2;
}
else
{
size_t x_3; 
x_3 = lean_ctor_get_usize(x_1, 2);
return x_3;
}
}
}
lean_object* l_Lean_Name_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Init_LeanInit___instance__2___closed__1;
return x_1;
}
}
lean_object* lean_name_mk_string(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_string_hash(x_2);
x_5 = lean_usize_mix_hash(x_3, x_4);
x_6 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_usize(x_6, 2, x_5);
return x_6;
}
}
lean_object* lean_name_mk_numeral(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_usize_of_nat(x_2);
x_5 = lean_usize_mix_hash(x_3, x_4);
x_6 = lean_alloc_ctor(2, 2, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_usize(x_6, 2, x_5);
return x_6;
}
}
lean_object* l_Lean_mkNameSimple(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_name_mk_string(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Name_beq_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_9 = lean_apply_2(x_6, x_1, x_2);
return x_9;
}
}
case 1:
{
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_usize(x_2, 2);
lean_dec(x_2);
x_16 = lean_box_usize(x_12);
x_17 = lean_box_usize(x_15);
x_18 = lean_apply_6(x_4, x_10, x_11, x_16, x_13, x_14, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_apply_2(x_6, x_1, x_2);
return x_19;
}
}
default: 
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get_usize(x_2, 2);
lean_dec(x_2);
x_26 = lean_box_usize(x_22);
x_27 = lean_box_usize(x_25);
x_28 = lean_apply_6(x_5, x_20, x_21, x_26, x_23, x_24, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_5);
x_29 = lean_apply_2(x_6, x_1, x_2);
return x_29;
}
}
}
}
}
lean_object* l_Lean_Name_beq_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_beq_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Name_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_name_eq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Name_Init_LeanInit___instance__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Name_Init_LeanInit___instance__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_Init_LeanInit___instance__3___closed__1;
return x_1;
}
}
lean_object* l_Lean_Name_toStringWithSep_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_12 = lean_box_usize(x_11);
x_13 = lean_apply_2(x_3, x_10, x_12);
return x_13;
}
else
{
lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_16 = lean_box_usize(x_15);
x_17 = lean_apply_3(x_5, x_9, x_14, x_16);
return x_17;
}
}
default: 
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_21 = lean_box_usize(x_20);
x_22 = lean_apply_2(x_4, x_19, x_21);
return x_22;
}
else
{
lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_25 = lean_box_usize(x_24);
x_26 = lean_apply_3(x_6, x_18, x_23, x_25);
return x_26;
}
}
}
}
}
lean_object* l_Lean_Name_toStringWithSep_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_toStringWithSep_match__1___rarg), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Name_toStringWithSep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[anonymous]");
return x_1;
}
}
lean_object* l_Lean_Name_toStringWithSep(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = l_Lean_Name_toStringWithSep___closed__1;
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Name_toStringWithSep(x_1, x_4);
x_8 = lean_string_append(x_7, x_1);
x_9 = lean_string_append(x_8, x_6);
lean_dec(x_6);
return x_9;
}
}
default: 
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Nat_repr(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Name_toStringWithSep(x_1, x_10);
x_15 = lean_string_append(x_14, x_1);
x_16 = l_Nat_repr(x_13);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
return x_17;
}
}
}
}
}
lean_object* l_Lean_Name_toStringWithSep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_toStringWithSep(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Name_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_System_FilePath_dirName___closed__1;
x_3 = l_Lean_Name_toStringWithSep(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Name_Init_LeanInit___instance__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Name_Init_LeanInit___instance__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_Init_LeanInit___instance__4___closed__1;
return x_1;
}
}
lean_object* l_Lean_Name_append_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_2, 2);
lean_dec(x_2);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_4(x_4, x_1, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_2, 2);
lean_dec(x_2);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_4(x_5, x_1, x_12, x_13, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Name_append_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_append_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Name_append(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_inc(x_1);
return x_1;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Name_append(x_1, x_3);
x_6 = lean_name_mk_string(x_5, x_4);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Name_append(x_1, x_7);
x_10 = lean_name_mk_numeral(x_9, x_8);
return x_10;
}
}
}
}
lean_object* l_Lean_Name_append___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_append(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Name_Init_LeanInit___instance__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_append___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Name_Init_LeanInit___instance__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Name_Init_LeanInit___instance__5___closed__1;
return x_1;
}
}
lean_object* l_Lean_Name_capitalize_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_7 = lean_box_usize(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Name_capitalize_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_capitalize_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Name_capitalize(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_String_capitalize(x_3);
x_5 = lean_name_mk_string(x_2, x_4);
return x_5;
}
else
{
return x_1;
}
}
}
lean_object* l_Lean_Name_appendAfter_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_8 = lean_box_usize(x_7);
x_9 = lean_apply_4(x_3, x_5, x_6, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l_Lean_Name_appendAfter_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_appendAfter_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Name_appendAfter(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_string_append(x_4, x_2);
lean_dec(x_2);
x_6 = lean_name_mk_string(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_name_mk_string(x_1, x_2);
return x_7;
}
}
}
lean_object* l_Lean_Name_appendIndexAfter_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_8 = lean_box_usize(x_7);
x_9 = lean_apply_4(x_3, x_5, x_6, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l_Lean_Name_appendIndexAfter_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_appendIndexAfter_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Name_appendIndexAfter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
lean_object* l_Lean_Name_appendIndexAfter(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Name_appendIndexAfter___closed__1;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Nat_repr(x_2);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_name_mk_string(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Nat_repr(x_2);
x_11 = l_Lean_Name_appendIndexAfter___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_name_mk_string(x_1, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Name_appendBefore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_4(x_4, x_7, x_8, x_10, x_2);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_4(x_5, x_12, x_13, x_15, x_2);
return x_16;
}
}
}
}
lean_object* l_Lean_Name_appendBefore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_appendBefore_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Name_appendBefore(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_name_mk_string(x_3, x_2);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_string_append(x_2, x_6);
lean_dec(x_6);
x_8 = lean_name_mk_string(x_5, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_name_mk_string(x_9, x_2);
x_12 = lean_name_mk_numeral(x_11, x_10);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_NameGenerator_namePrefix___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_uniq");
return x_1;
}
}
static lean_object* _init_l_Lean_NameGenerator_namePrefix___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_NameGenerator_namePrefix___default___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_NameGenerator_namePrefix___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameGenerator_namePrefix___default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_NameGenerator_idx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_NameGenerator_Init_LeanInit___instance__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameGenerator_namePrefix___default___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_NameGenerator_Init_LeanInit___instance__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameGenerator_Init_LeanInit___instance__6___closed__1;
return x_1;
}
}
lean_object* l_Lean_NameGenerator_curr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_name_mk_numeral(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_NameGenerator_next(lean_object* x_1) {
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
lean_object* l_Lean_NameGenerator_mkChild(lean_object* x_1) {
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
x_5 = lean_name_mk_numeral(x_3, x_4);
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
x_12 = lean_name_mk_numeral(x_10, x_11);
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
lean_object* l_Lean_mkFreshId___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_name_mk_numeral(x_6, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_7, x_10);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_11);
x_12 = lean_apply_1(x_9, x_4);
x_13 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_8);
x_14 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
lean_inc(x_16);
lean_inc(x_15);
x_17 = lean_name_mk_numeral(x_15, x_16);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_16, x_19);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_apply_1(x_18, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_Init_Control_Reader___instance__4___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_17);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
}
lean_object* l_Lean_mkFreshId___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_mkFreshId___rarg___lambda__1), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_mkFreshId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshId___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_monadNameGeneratorLift___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_monadNameGeneratorLift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_monadNameGeneratorLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_monadNameGeneratorLift___rarg), 2, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_splitAux___closed__1;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Init_LeanInit___instance__7___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_SourceInfo_leading___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_SourceInfo_pos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_SourceInfo_trailing___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_choiceKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("choice");
return x_1;
}
}
static lean_object* _init_l_Lean_choiceKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_choiceKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_choiceKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_choiceKind___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_nullKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Lean_nullKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_nullKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_nullKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_nullKind___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_identKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l_Lean_identKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_identKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_identKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_identKind___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_strLitKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("strLit");
return x_1;
}
}
static lean_object* _init_l_Lean_strLitKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_strLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_strLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_strLitKind___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_charLitKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("charLit");
return x_1;
}
}
static lean_object* _init_l_Lean_charLitKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_charLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_charLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_charLitKind___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_numLitKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("numLit");
return x_1;
}
}
static lean_object* _init_l_Lean_numLitKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_numLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_numLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_numLitKind___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_nameLitKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nameLit");
return x_1;
}
}
static lean_object* _init_l_Lean_nameLitKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_nameLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_nameLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_nameLitKind___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_fieldIdxKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fieldIdx");
return x_1;
}
}
static lean_object* _init_l_Lean_fieldIdxKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_fieldIdxKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_fieldIdxKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_fieldIdxKind___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_interpolatedStrLitKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("interpolatedStrLitKind");
return x_1;
}
}
static lean_object* _init_l_Lean_interpolatedStrLitKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_interpolatedStrLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_interpolatedStrLitKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_interpolatedStrLitKind___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_interpolatedStrKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("interpolatedStrKind");
return x_1;
}
}
static lean_object* _init_l_Lean_interpolatedStrKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_interpolatedStrKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_interpolatedStrKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_interpolatedStrKind___closed__2;
return x_1;
}
}
lean_object* l_Lean_Syntax_getKind_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_2, x_8, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_4(x_5, x_14, x_15, x_16, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Syntax_getKind_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getKind_match__1___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Syntax_getKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("missing");
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_getKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Syntax_getKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getKind(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getKind___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_name_mk_string(x_5, x_4);
return x_6;
}
default: 
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_identKind;
return x_7;
}
}
}
}
lean_object* l_Lean_Syntax_setKind_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_setKind_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_setKind_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_setKind(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
uint8_t l_Lean_Syntax_isOfKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Syntax_getKind(x_1);
x_4 = lean_name_eq(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_isOfKind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_getArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_getArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_getArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Init_LeanInit___instance__9;
x_5 = lean_array_get(x_4, x_3, x_2);
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
lean_object* l_Lean_Syntax_getArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_getOp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getOp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getOp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_getArgs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_getArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getArgs_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_getArgs(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Array_empty___closed__1;
return x_3;
}
}
}
lean_object* l_Lean_Syntax_getArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getHeadInfo_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_2, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_4(x_3, x_13, x_14, x_15, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Syntax_getHeadInfo_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getHeadInfo_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_findSomeMAux___at_Lean_Syntax_getHeadInfo___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = l_Lean_Syntax_getHeadInfo(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
lean_object* l_Lean_Syntax_getHeadInfo(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_findSomeMAux___at_Lean_Syntax_getHeadInfo___spec__1(x_3, x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
lean_object* l_Array_findSomeMAux___at_Lean_Syntax_getHeadInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findSomeMAux___at_Lean_Syntax_getHeadInfo___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_getHeadInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_reservedMacroScope() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_firstFrontendMacroScope___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_reservedMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_firstFrontendMacroScope() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_firstFrontendMacroScope___closed__1;
return x_1;
}
}
lean_object* l_Lean_Name_hasMacroScopes_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_1);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_9 = lean_box_usize(x_8);
x_10 = lean_apply_3(x_2, x_6, x_7, x_9);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_14 = lean_box_usize(x_13);
x_15 = lean_apply_3(x_3, x_11, x_12, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Name_hasMacroScopes_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_hasMacroScopes_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Name_hasMacroScopes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_hyg");
return x_1;
}
}
uint8_t l_Lean_Name_hasMacroScopes(lean_object* x_1) {
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
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Name_hasMacroScopes___closed__1;
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
x_1 = x_6;
goto _start;
}
}
}
}
lean_object* l_Lean_Name_hasMacroScopes___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_3(x_2, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_3(x_3, x_12, x_13, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.LeanInit");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Init.LeanInit.0.Lean.eraseMacroScopesAux");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__1;
x_2 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__2;
x_3 = lean_unsigned_to_nat(353u);
x_4 = lean_unsigned_to_nat(24u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_@");
return x_1;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Init_LeanInit___instance__1;
x_3 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__4;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5;
x_8 = lean_string_dec_eq(x_6, x_7);
if (x_8 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
lean_inc(x_5);
return x_5;
}
}
default: 
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 0);
x_1 = x_10;
goto _start;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* lean_erase_macro_scopes(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux(x_1);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_simpMacroScopesAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_7 = lean_box_usize(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_simpMacroScopesAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_simpMacroScopesAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_simpMacroScopesAux(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Init_LeanInit_0__Lean_simpMacroScopesAux(x_2);
x_5 = lean_name_mk_numeral(x_4, x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux(x_1);
lean_dec(x_1);
return x_6;
}
}
}
lean_object* lean_simp_macro_scopes(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_0__Lean_simpMacroScopesAux(x_1);
return x_3;
}
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Init_LeanInit___instance__10___closed__1;
return x_1;
}
}
lean_object* l_List_foldl___at_Lean_MacroScopesView_review___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_name_mk_numeral(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Lean_MacroScopesView_review(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = l_List_isEmpty___rarg(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5;
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_Name_append(x_6, x_7);
lean_dec(x_6);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Name_append(x_8, x_9);
lean_dec(x_8);
x_11 = l_Lean_Name_hasMacroScopes___closed__1;
x_12 = lean_name_mk_string(x_10, x_11);
x_13 = l_List_foldl___at_Lean_MacroScopesView_review___spec__1(x_12, x_2);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
return x_14;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_assembleParts_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_apply_1(x_3, x_2);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_apply_2(x_6, x_1, x_2);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_usize(x_8, 2);
lean_dec(x_8);
x_14 = lean_box_usize(x_13);
x_15 = lean_apply_5(x_4, x_11, x_12, x_14, x_10, x_2);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get_usize(x_8, 2);
lean_dec(x_8);
x_20 = lean_box_usize(x_19);
x_21 = lean_apply_5(x_5, x_17, x_18, x_20, x_16, x_2);
return x_21;
}
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_assembleParts_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_assembleParts_match__1___rarg), 6, 0);
return x_2;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_assembleParts___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Init.LeanInit.0.Lean.assembleParts");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_assembleParts___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__1;
x_2 = l___private_Init_LeanInit_0__Lean_assembleParts___closed__1;
x_3 = lean_unsigned_to_nat(387u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_assembleParts(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = l_Lean_Init_LeanInit___instance__1;
x_5 = l___private_Init_LeanInit_0__Lean_assembleParts___closed__2;
x_6 = lean_panic_fn(x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_name_mk_string(x_2, x_8);
x_1 = x_7;
x_2 = x_9;
goto _start;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_name_mk_numeral(x_2, x_12);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_extractImported_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_apply_2(x_5, x_1, x_2);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_5(x_3, x_1, x_7, x_8, x_10, x_2);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_5(x_4, x_1, x_12, x_13, x_15, x_2);
return x_16;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_extractImported_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_extractImported_match__1___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_extractImported___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Init.LeanInit.0.Lean.extractImported");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_extractImported___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__1;
x_2 = l___private_Init_LeanInit_0__Lean_extractImported___closed__1;
x_3 = lean_unsigned_to_nat(396u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_extractImported(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_Lean_Init_LeanInit___instance__10;
x_6 = l___private_Init_LeanInit_0__Lean_extractImported___closed__2;
x_7 = lean_panic_fn(x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5;
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
x_3 = x_8;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = l___private_Init_LeanInit_0__Lean_assembleParts(x_4, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_2);
lean_ctor_set(x_16, 3, x_1);
return x_16;
}
}
default: 
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_4);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_extractMainModule_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_apply_2(x_5, x_1, x_2);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_5(x_3, x_1, x_7, x_8, x_10, x_2);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_5(x_4, x_1, x_12, x_13, x_15, x_2);
return x_16;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_extractMainModule_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_extractMainModule_match__1___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_extractMainModule___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Init.LeanInit.0.Lean.extractMainModule");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_extractMainModule___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__1;
x_2 = l___private_Init_LeanInit_0__Lean_extractMainModule___closed__1;
x_3 = lean_unsigned_to_nat(405u);
x_4 = lean_unsigned_to_nat(33u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_extractMainModule(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = l_Lean_Init_LeanInit___instance__10;
x_5 = l___private_Init_LeanInit_0__Lean_extractMainModule___closed__2;
x_6 = lean_panic_fn(x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5;
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_3);
x_2 = x_7;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = l___private_Init_LeanInit_0__Lean_assembleParts(x_3, x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_1);
return x_15;
}
}
default: 
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_box(0);
x_17 = l___private_Init_LeanInit_0__Lean_assembleParts(x_3, x_16);
x_18 = lean_box(0);
x_19 = l___private_Init_LeanInit_0__Lean_extractImported(x_1, x_17, x_2, x_18);
return x_19;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_extractMacroScopesAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_apply_2(x_5, x_1, x_2);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_4(x_4, x_7, x_8, x_10, x_2);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_4(x_3, x_12, x_13, x_15, x_2);
return x_16;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_extractMacroScopesAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_extractMacroScopesAux_match__1___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Init.LeanInit.0.Lean.extractMacroScopesAux");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__1;
x_2 = l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__1;
x_3 = lean_unsigned_to_nat(410u);
x_4 = lean_unsigned_to_nat(29u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_extractMacroScopesAux(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_3 = l_Lean_Init_LeanInit___instance__10;
x_4 = l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__2;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = l___private_Init_LeanInit_0__Lean_extractMainModule(x_2, x_6, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_1 = x_9;
x_2 = x_11;
goto _start;
}
}
}
}
lean_object* l_Lean_extractMacroScopes(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l___private_Init_LeanInit_0__Lean_extractMacroScopesAux(x_1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_addMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Name_hasMacroScopes(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5;
x_6 = lean_name_mk_string(x_2, x_5);
x_7 = l_Lean_Name_append(x_6, x_1);
lean_dec(x_6);
x_8 = l_Lean_Name_hasMacroScopes___closed__1;
x_9 = lean_name_mk_string(x_7, x_8);
x_10 = lean_name_mk_numeral(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_2);
x_11 = l_Lean_extractMacroScopes(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_name_eq(x_15, x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_18 = l_Lean_Name_append(x_14, x_15);
lean_dec(x_14);
x_19 = l_List_foldl___at_Lean_MacroScopesView_review___spec__1(x_18, x_16);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_11, 3, x_21);
lean_ctor_set(x_11, 2, x_1);
lean_ctor_set(x_11, 1, x_19);
x_22 = l_Lean_MacroScopesView_review(x_11);
return x_22;
}
else
{
lean_object* x_23; 
lean_free_object(x_11);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_23 = lean_name_mk_numeral(x_2, x_3);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
x_27 = lean_ctor_get(x_11, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_28 = lean_name_eq(x_26, x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_29 = l_Lean_Name_append(x_25, x_26);
lean_dec(x_25);
x_30 = l_List_foldl___at_Lean_MacroScopesView_review___spec__1(x_29, x_27);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_1);
lean_ctor_set(x_33, 3, x_32);
x_34 = l_Lean_MacroScopesView_review(x_33);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_35 = lean_name_mk_numeral(x_2, x_3);
return x_35;
}
}
}
}
}
lean_object* l_Lean_MonadQuotation_addMacroScope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_addMacroScope(x_2, x_3, x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_MonadQuotation_addMacroScope___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_MonadQuotation_addMacroScope___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_MonadQuotation_addMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_MonadQuotation_addMacroScope___rarg___lambda__2), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_4);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_MonadQuotation_addMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MonadQuotation_addMacroScope___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_defaultMaxRecDepth() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(512u);
return x_1;
}
}
static lean_object* _init_l_Lean_maxRecDepthErrorMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum recursion depth has been reached (use `set_option maxRecDepth <num>` to increase limit)");
return x_1;
}
}
static lean_object* _init_l_Lean_maxRecDepthErrorMessage() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepthErrorMessage___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Macro_MacroEnvPointed() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Macro_Init_LeanInit___instance__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Macro_Context_currRecDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Macro_Context_maxRecDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_defaultMaxRecDepth;
return x_1;
}
}
lean_object* l_Lean_Macro_addMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_addMacroScope(x_4, x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
lean_object* l_Lean_Macro_throwUnsupported___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Macro_throwUnsupported(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Macro_throwUnsupported___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Macro_throwUnsupported___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Macro_throwUnsupported(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Macro_throwError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Macro_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Macro_throwError___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Macro_throwError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Macro_throwError___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Macro_withFreshMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 2);
lean_dec(x_7);
lean_ctor_set(x_2, 2, x_3);
x_8 = lean_apply_2(x_1, x_2, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_11);
lean_ctor_set(x_13, 4, x_12);
x_14 = lean_apply_2(x_1, x_13, x_5);
return x_14;
}
}
}
lean_object* l_Lean_Macro_withFreshMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Macro_withFreshMacroScope___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Macro_withIncRecDepth___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 3, x_8);
x_9 = lean_apply_2(x_1, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_13, x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_14);
x_18 = lean_apply_2(x_1, x_17, x_4);
return x_18;
}
}
}
lean_object* l_Lean_Macro_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_6);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_Macro_withIncRecDepth___rarg___lambda__1(x_2, x_8, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = l_Lean_maxRecDepthErrorMessage;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
}
lean_object* l_Lean_Macro_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Macro_withIncRecDepth___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Macro_withIncRecDepth___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Macro_withIncRecDepth___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 2);
lean_dec(x_8);
lean_ctor_set(x_3, 2, x_4);
x_9 = lean_apply_2(x_2, x_3, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 4, x_13);
x_15 = lean_apply_2(x_2, x_14, x_6);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Macro_Init_LeanInit___instance__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Macro_Init_LeanInit___instance__12___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Macro_Init_LeanInit___instance__12___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Macro_Init_LeanInit___instance__12___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Macro_Init_LeanInit___instance__12___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Macro_Init_LeanInit___instance__12___lambda__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Macro_Init_LeanInit___instance__12___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Macro_Init_LeanInit___instance__12___closed__1;
x_2 = l_Lean_Macro_Init_LeanInit___instance__12___closed__2;
x_3 = l_Lean_Macro_Init_LeanInit___instance__12___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Macro_Init_LeanInit___instance__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Macro_Init_LeanInit___instance__12___closed__4;
return x_1;
}
}
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Macro_Init_LeanInit___instance__12___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Macro_Init_LeanInit___instance__12___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Macro_Init_LeanInit___instance__12___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Macro_Init_LeanInit___instance__13___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
lean_object* l_Lean_Macro_Init_LeanInit___instance__13___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Macro_Init_LeanInit___instance__13___rarg___lambda__1), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_3(x_2, lean_box(0), x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Macro_Init_LeanInit___instance__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Macro_Init_LeanInit___instance__13___rarg___lambda__2), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
lean_object* l_Lean_Macro_Init_LeanInit___instance__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Macro_Init_LeanInit___instance__13___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Macro_mkMacroEnvImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = x_1;
return x_2;
}
}
lean_object* l_Lean_Macro_mkMacroEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_Macro_mkMacroEnv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Macro_mkMacroEnv(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Macro_expandMacroNotAvailable_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expandMacro has not been set");
return x_1;
}
}
lean_object* l_Lean_Macro_expandMacroNotAvailable_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Macro_expandMacroNotAvailable_x3f___closed__1;
x_5 = l_Lean_Macro_throwError___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Macro_expandMacroNotAvailable_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Macro_expandMacroNotAvailable_x3f(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Macro_mkMacroEnvSimple___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Macro_expandMacroNotAvailable_x3f___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Macro_mkMacroEnvSimple___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Macro_mkMacroEnvSimple___closed__1;
x_2 = x_1;
return x_2;
}
}
static lean_object* _init_l_Lean_Macro_mkMacroEnvSimple() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Macro_mkMacroEnvSimple___closed__2;
return x_1;
}
}
lean_object* l_Lean_Macro_expandMacro_x3fImp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = x_4;
x_6 = lean_apply_3(x_5, x_1, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Macro_expandMacro_x3f___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Macro_expandMacro_x3f___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Macro_expandMacro_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Macro_expandMacro_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_expandMacros_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_expandMacros_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_expandMacros_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_expandMacros_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_2, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_expandMacros_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_expandMacros_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___at_Lean_expandMacros___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
lean_inc(x_3);
x_13 = l_Lean_expandMacros(x_12, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
x_18 = x_14;
x_19 = lean_array_fset(x_11, x_1, x_18);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_19;
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Lean_expandMacros___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 3, x_8);
x_9 = x_1;
x_10 = lean_apply_2(x_9, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_ctor_get(x_3, 3);
x_15 = lean_ctor_get(x_3, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_14, x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set(x_18, 4, x_15);
x_19 = x_1;
x_20 = lean_apply_2(x_19, x_18, x_4);
return x_20;
}
}
}
lean_object* l_Lean_expandMacros(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Macro_expandMacro_x3fImp(x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = x_5;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_closure((void*)(l_Array_umapMAux___at_Lean_expandMacros___spec__1), 4, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 4);
lean_inc(x_15);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_free_object(x_6);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_1, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = l_Lean_expandMacros___lambda__1(x_13, x_20, x_2, x_9);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_1, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_1);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = l_Lean_expandMacros___lambda__1(x_13, x_31, x_2, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
x_42 = l_Lean_maxRecDepthErrorMessage;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_43);
return x_6;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_44);
lean_dec(x_6);
x_45 = x_5;
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_alloc_closure((void*)(l_Array_umapMAux___at_Lean_expandMacros___spec__1), 4, 2);
lean_closure_set(x_47, 0, x_46);
lean_closure_set(x_47, 1, x_45);
x_48 = lean_ctor_get(x_2, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 4);
lean_inc(x_49);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_51 = x_1;
} else {
 lean_dec_ref(x_1);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
x_53 = l_Lean_expandMacros___lambda__1(x_47, x_52, x_2, x_44);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_51;
}
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_54);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_51);
lean_dec(x_4);
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_47);
lean_dec(x_4);
lean_dec(x_2);
x_63 = l_Lean_maxRecDepthErrorMessage;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_44);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_66 = lean_ctor_get(x_6, 1);
lean_inc(x_66);
lean_dec(x_6);
x_67 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
lean_dec(x_7);
x_1 = x_67;
x_3 = x_66;
goto _start;
}
}
else
{
uint8_t x_69; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_6);
if (x_69 == 0)
{
return x_6;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_6, 0);
x_71 = lean_ctor_get(x_6, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_6);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_2);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_3);
return x_73;
}
}
}
lean_object* l_Lean_expandMacros___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_expandMacros___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_mkIdentFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_Syntax_getHeadInfo(x_1);
x_4 = l_System_FilePath_dirName___closed__1;
lean_inc(x_2);
x_5 = l_Lean_Name_toStringWithSep(x_4, x_2);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_6);
x_9 = lean_box(0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_11 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_2);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_9);
return x_13;
}
}
}
lean_object* l_Lean_mkIdentFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkIdentFrom(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkCIdentFrom___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_internal");
return x_1;
}
}
static lean_object* _init_l_Lean_mkCIdentFrom___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkCIdentFrom___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkCIdentFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_Lean_Syntax_getHeadInfo(x_1);
x_4 = l_Lean_mkCIdentFrom___closed__2;
x_5 = l_Lean_reservedMacroScope;
lean_inc(x_2);
x_6 = l_Lean_addMacroScope(x_4, x_2, x_5);
x_7 = l_System_FilePath_dirName___closed__1;
lean_inc(x_6);
x_8 = l_Lean_Name_toStringWithSep(x_7, x_6);
x_9 = lean_string_utf8_byte_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_16 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_6);
lean_ctor_set(x_16, 3, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_6);
lean_ctor_set(x_18, 3, x_14);
return x_18;
}
}
}
lean_object* l_Lean_mkCIdentFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkCIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_mkCIdentFrom(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkAtomFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getHeadInfo(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_5 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
lean_object* l_Lean_mkAtomFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkAtomFrom(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_identToAtom_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_identToAtom_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_identToAtom_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_identToAtom(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_erase_macro_scopes(x_3);
x_5 = l_System_FilePath_dirName___closed__1;
x_6 = l_Lean_Name_toStringWithSep(x_5, x_4);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
return x_1;
}
}
}
lean_object* lean_mk_syntax_ident(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_System_FilePath_dirName___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Name_toStringWithSep(x_2, x_1);
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_4);
x_7 = lean_box(0);
x_8 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_9 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_1);
lean_ctor_set(x_9, 3, x_7);
return x_9;
}
}
lean_object* l_Lean_mkNullNode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_nullKind;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_mkSepArray_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_mkSepArray_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkSepArray_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_mkSepArray_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_mkSepArray_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkSepArray_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_push(x_8, x_7);
x_14 = lean_box(0);
x_15 = lean_apply_3(x_10, x_13, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
return x_16;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_1);
x_21 = lean_array_push(x_8, x_1);
x_22 = lean_array_push(x_21, x_7);
x_23 = lean_box(0);
x_24 = lean_apply_3(x_10, x_22, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
return x_25;
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = x_4 + x_27;
x_4 = x_28;
x_5 = x_26;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkSepArray___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkSepArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Lean_mkSepArray___closed__1;
x_7 = l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1(x_2, x_1, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_mkSepArray___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkSepArray(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkSepStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_mkSepArray(x_1, x_2);
x_4 = l_Lean_nullKind;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_mkSepStx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkSepStx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkOptionalNode_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_mkOptionalNode_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkOptionalNode_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_mkOptionalNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkOptionalNode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_mkOptionalNode(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_mkOptionalNode___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_mkOptionalNode___closed__2;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_Lean_nullKind;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
static lean_object* _init_l_Lean_mkAppStx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_mkAppStx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAppStx___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkAppStx___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_mkAppStx___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_mkAppStx___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkAppStx___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Lean_mkAppStx___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__4;
x_2 = l_Lean_mkAppStx___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkAppStx___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Lean_mkAppStx___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_mkAppStx___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkAppStx___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_mkAppStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_nullKind;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Lean_mkAppStx___closed__9;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_6, x_4);
x_8 = l_Lean_mkAppStx___closed__8;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_mkHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l_Lean_mkHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_mkHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Name_appendIndexAfter___closed__1;
x_3 = l_Lean_mkAtomFrom(x_1, x_2);
x_4 = l_Lean_mkOptionalNode___closed__2;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_Lean_mkHole___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_mkHole___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHole(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_mkCAppStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_mkCIdentFrom(x_3, x_1);
x_5 = l_Lean_mkAppStx(x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_mkStxLit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Lean_mkOptionalNode___closed__2;
x_6 = lean_array_push(x_5, x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_mkStxStrLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_String_quote(x_1);
x_4 = l_Lean_strLitKind;
x_5 = l_Lean_mkStxLit(x_4, x_3, x_2);
return x_5;
}
}
lean_object* l_Lean_mkStxStrLit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStxStrLit(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkStxNumLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_numLitKind;
x_4 = l_Lean_mkStxLit(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeBinLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_2);
x_6 = 48;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 49;
x_9 = x_5 == x_8;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_mul(x_12, x_3);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
x_2 = x_11;
x_3 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_mul(x_18, x_3);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_3);
return x_21;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeBinLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_0__Lean_Syntax_decodeBinLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeOctalLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_2);
x_6 = 48;
x_7 = x_6 <= x_5;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 55;
x_10 = x_5 <= x_9;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
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
lean_object* x_20; 
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeOctalLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_0__Lean_Syntax_decodeOctalLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; uint32_t x_44; uint8_t x_45; 
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = lean_string_utf8_next(x_1, x_2);
x_44 = 48;
x_45 = x_44 <= x_3;
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
x_5 = x_46;
goto block_43;
}
else
{
uint32_t x_47; uint8_t x_48; 
x_47 = 57;
x_48 = x_3 <= x_47;
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_box(0);
x_5 = x_49;
goto block_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_uint32_to_nat(x_3);
x_51 = lean_unsigned_to_nat(48u);
x_52 = lean_nat_sub(x_50, x_51);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
block_43:
{
uint32_t x_6; uint8_t x_7; 
lean_dec(x_5);
x_6 = 97;
x_7 = x_6 <= x_3;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 65;
x_9 = x_8 <= x_3;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_box(0);
return x_10;
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 70;
x_12 = x_3 <= x_11;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_uint32_to_nat(x_3);
x_15 = lean_unsigned_to_nat(10u);
x_16 = lean_nat_add(x_15, x_14);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(65u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 102;
x_22 = x_3 <= x_21;
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 65;
x_24 = x_23 <= x_3;
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_box(0);
return x_25;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 70;
x_27 = x_3 <= x_26;
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_4);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_uint32_to_nat(x_3);
x_30 = lean_unsigned_to_nat(10u);
x_31 = lean_nat_add(x_30, x_29);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(65u);
x_33 = lean_nat_sub(x_31, x_32);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_uint32_to_nat(x_3);
x_37 = lean_unsigned_to_nat(10u);
x_38 = lean_nat_add(x_37, x_36);
lean_dec(x_36);
x_39 = lean_unsigned_to_nat(97u);
x_40 = lean_nat_sub(x_38, x_39);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit(x_1, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(16u);
x_11 = lean_nat_mul(x_10, x_3);
lean_dec(x_3);
x_12 = lean_nat_add(x_11, x_8);
lean_dec(x_8);
lean_dec(x_11);
x_2 = x_9;
x_3 = x_12;
goto _start;
}
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeDecimalLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_2);
x_6 = 48;
x_7 = x_6 <= x_5;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = 57;
x_10 = x_5 <= x_9;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
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
lean_object* x_20; 
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_3);
return x_20;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeDecimalLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_0__Lean_Syntax_decodeDecimalLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Syntax_decodeNatLitVal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeNatLitVal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = 48;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = l_Char_isDigit(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Init_LeanInit_0__Lean_Syntax_decodeDecimalLitAux(x_1, x_3, x_3);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_2, x_11);
lean_dec(x_2);
if (x_12 == 0)
{
uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_string_utf8_get(x_1, x_11);
x_14 = 120;
x_15 = x_13 == x_14;
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 88;
x_17 = x_13 == x_16;
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; uint32_t x_20; uint8_t x_21; uint8_t x_22; 
x_18 = 98;
x_19 = x_13 == x_18;
x_20 = 66;
x_21 = x_13 == x_20;
if (x_19 == 0)
{
uint8_t x_39; 
x_39 = 0;
x_22 = x_39;
goto block_38;
}
else
{
uint8_t x_40; 
x_40 = 1;
x_22 = x_40;
goto block_38;
}
block_38:
{
if (x_21 == 0)
{
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 111;
x_24 = x_13 == x_23;
if (x_24 == 0)
{
uint32_t x_25; uint8_t x_26; 
x_25 = 79;
x_26 = x_13 == x_25;
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Char_isDigit(x_13);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = l___private_Init_LeanInit_0__Lean_Syntax_decodeDecimalLitAux(x_1, x_3, x_3);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_unsigned_to_nat(2u);
x_31 = l___private_Init_LeanInit_0__Lean_Syntax_decodeOctalLitAux(x_1, x_30, x_3);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = l___private_Init_LeanInit_0__Lean_Syntax_decodeOctalLitAux(x_1, x_32, x_3);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(2u);
x_35 = l___private_Init_LeanInit_0__Lean_Syntax_decodeBinLitAux(x_1, x_34, x_3);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(2u);
x_37 = l___private_Init_LeanInit_0__Lean_Syntax_decodeBinLitAux(x_1, x_36, x_3);
return x_37;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(2u);
x_42 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux(x_1, x_41, x_3);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(2u);
x_44 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexLitAux(x_1, x_43, x_3);
return x_44;
}
}
else
{
lean_object* x_45; 
x_45 = l_Lean_Syntax_decodeNatLitVal___closed__1;
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_2);
x_46 = lean_box(0);
return x_46;
}
}
}
lean_object* l_Lean_Syntax_decodeNatLitVal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeNatLitVal(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isLit_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isLit_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isLit_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isLit_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
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
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Init_LeanInit___instance__9;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_4, x_12);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_box(0);
return x_16;
}
}
}
}
else
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
}
}
lean_object* l_Lean_Syntax_isLit_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isLit_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_isNatLitAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isNatLitAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isNatLitAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isNatLitAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isLit_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Syntax_decodeNatLitVal(x_5);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isNatLitAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_isNatLitAux(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_numLitKind;
x_3 = l_Lean_Syntax_isNatLitAux(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_isNatLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_fieldIdxKind;
x_3 = l_Lean_Syntax_isNatLitAux(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_isFieldIdx_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isFieldIdx_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isIdOrAtom_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_4(x_3, x_8, x_9, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
}
}
}
lean_object* l_Lean_Syntax_isIdOrAtom_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isIdOrAtom_x3f_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 3:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
}
}
}
lean_object* l_Lean_Syntax_isIdOrAtom_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isIdOrAtom_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_toNat_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_toNat_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_toNat_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_toNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_numLitKind;
x_3 = l_Lean_Syntax_isNatLitAux(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
return x_5;
}
}
}
lean_object* l_Lean_Syntax_toNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_toNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__5___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeQuotedChar_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeQuotedChar_match__6___rarg), 2, 0);
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
lean_object* l_Lean_Syntax_decodeQuotedChar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; uint32_t x_5; uint8_t x_6; 
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = lean_string_utf8_next(x_1, x_2);
x_5 = 92;
x_6 = x_3 == x_5;
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 34;
x_8 = x_3 == x_7;
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 39;
x_10 = x_3 == x_9;
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 114;
x_12 = x_3 == x_11;
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 110;
x_14 = x_3 == x_13;
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 116;
x_16 = x_3 == x_15;
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 120;
x_18 = x_3 == x_17;
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 117;
x_20 = x_3 == x_19;
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
x_22 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit(x_1, x_4);
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
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit(x_1, x_26);
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
lean_dec(x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit(x_1, x_31);
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
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit(x_1, x_36);
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
x_79 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit(x_1, x_4);
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
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Init_LeanInit_0__Lean_Syntax_decodeHexDigit(x_1, x_83);
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
lean_object* l_Lean_Syntax_decodeQuotedChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_decodeQuotedChar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeStrLitAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_6 = 34;
x_7 = x_4 == x_6;
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_1, x_5);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 92;
x_10 = x_4 == x_9;
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_string_push(x_3, x_4);
x_2 = x_5;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Syntax_decodeQuotedChar(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unbox_uint32(x_16);
lean_dec(x_16);
x_19 = lean_string_push(x_3, x_18);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
}
}
else
{
lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_3);
x_21 = lean_box(0);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_3);
return x_22;
}
}
}
lean_object* l_Lean_Syntax_decodeStrLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_decodeStrLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_decodeStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_String_splitAux___closed__1;
x_4 = l_Lean_Syntax_decodeStrLitAux(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_decodeStrLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeStrLit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isStrLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isStrLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isStrLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_strLitKind;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_String_splitAux___closed__1;
x_8 = l_Lean_Syntax_decodeStrLitAux(x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
}
lean_object* l_Lean_Syntax_isStrLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isStrLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeCharLit_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_decodeCharLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_decodeCharLit_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_decodeCharLit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 92;
x_5 = x_3 == x_4;
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
lean_object* l_Lean_Syntax_decodeCharLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeCharLit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isCharLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isCharLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isCharLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_charLitKind;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Syntax_decodeCharLit(x_5);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isCharLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isCharLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = l_Lean_isIdRest(x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; 
x_7 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
}
else
{
return x_3;
}
}
}
lean_object* l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_3, x_2);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = l_Lean_idEndEscape;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_8;
goto _start;
}
else
{
return x_3;
}
}
else
{
return x_3;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint32_t x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_string_utf8_get(x_1, x_2);
x_16 = l_Lean_idBeginEscape;
x_17 = x_15 == x_16;
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_isIdFirst(x_15);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_string_utf8_byte_size(x_1);
lean_inc(x_2);
x_21 = l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__1(x_1, x_20, x_2);
lean_dec(x_20);
x_22 = lean_string_utf8_extract(x_1, x_2, x_21);
lean_dec(x_2);
x_23 = lean_name_mk_string(x_3, x_22);
x_4 = x_21;
x_5 = x_23;
goto block_14;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_24 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_25 = lean_string_utf8_byte_size(x_1);
lean_inc(x_24);
x_26 = l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__2(x_1, x_25, x_24);
lean_dec(x_25);
x_27 = lean_string_utf8_get(x_1, x_26);
x_28 = l_Lean_idEndEscape;
x_29 = x_27 == x_28;
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_3);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_string_utf8_next(x_1, x_26);
x_32 = lean_string_utf8_extract(x_1, x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_33 = lean_name_mk_string(x_3, x_32);
x_4 = x_31;
x_5 = x_33;
goto block_14;
}
}
block_14:
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_4);
x_7 = 46;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_utf8_at_end(x_1, x_4);
lean_dec(x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_2 = x_12;
x_3 = x_5;
goto _start;
}
}
}
}
lean_object* l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_decodeNameLit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 96;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_box(0);
x_9 = l___private_Init_LeanInit_0__Lean_Syntax_decodeNameLitAux(x_1, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_decodeNameLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_decodeNameLit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isNameLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isNameLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isNameLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_nameLitKind;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Syntax_decodeNameLit(x_5);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_isNameLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isNameLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_hasArgs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_hasArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_hasArgs_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Syntax_hasArgs(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
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
lean_object* l_Lean_Syntax_hasArgs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_hasArgs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_identToStrLit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_identToStrLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_identToStrLit_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_identToStrLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_System_FilePath_dirName___closed__1;
x_5 = l_Lean_Name_toStringWithSep(x_4, x_3);
x_6 = l_Lean_mkStxStrLit(x_5, x_2);
lean_dec(x_5);
return x_6;
}
else
{
return x_1;
}
}
}
lean_object* l_Lean_Syntax_strLitToAtom_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_strLitToAtom_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_strLitToAtom_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_strLitToAtom(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isStrLit_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Syntax_getHeadInfo(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Init_LeanInit___instance__8;
x_6 = l_Option_get_x21___rarg___closed__4;
x_7 = lean_panic_fn(x_5, x_6);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
}
}
lean_object* l_Lean_Syntax_strLitToAtom___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_strLitToAtom(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isAtom_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isAtom_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isAtom_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Syntax_isAtom(lean_object* x_1) {
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
lean_object* l_Lean_Syntax_isAtom___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isAtom(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_isToken_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isToken_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isToken_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Syntax_isToken(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_String_trim(x_3);
x_5 = l_String_trim(x_1);
x_6 = lean_string_dec_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isToken___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_isToken(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Syntax_isIdent_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_isIdent_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isIdent_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Syntax_isIdent(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
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
lean_object* l_Lean_Syntax_isIdent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isIdent(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getId_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Syntax_getId_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getId_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_getId(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
}
lean_object* l_Lean_Syntax_getId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isNone_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isNone_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isNone_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Syntax_isNone(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_nullKind;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
lean_object* l_Lean_Syntax_isNone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Syntax_isNone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_getOptional_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_getOptional_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getOptional_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_nullKind;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Init_LeanInit___instance__9;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_11, x_3, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
}
}
lean_object* l_Lean_Syntax_getOptional_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptional_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_getOptionalIdent_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_getOptionalIdent_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_getOptionalIdent_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object* x_1) {
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
lean_object* l_Lean_Syntax_getOptionalIdent_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getOptionalIdent_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_findAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_2, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_findAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_findAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_findSomeMAux___at_Lean_Syntax_findAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_Syntax_findAux(x_1, x_7);
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
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_Syntax_findAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_findSomeMAux___at_Lean_Syntax_findAux___spec__1(x_1, x_3, x_6);
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_9 = lean_apply_1(x_1, x_2);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
}
}
lean_object* l_Array_findSomeMAux___at_Lean_Syntax_findAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findSomeMAux___at_Lean_Syntax_findAux___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_findAux(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Init_Core___instance__1___closed__1;
return x_1;
}
}
lean_object* l_Lean_Init_LeanInit___instance__15(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_3 = l_Lean_mkStxStrLit(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Init_LeanInit___instance__15___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Init_LeanInit___instance__15(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Init_LeanInit___instance__16(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_numLitKind;
x_4 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_5 = l_Lean_mkStxLit(x_3, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__17___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("String");
return x_1;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__17___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Init_LeanInit___instance__17___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__17___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toSubstring");
return x_1;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__17___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__17___closed__2;
x_2 = l_Lean_Init_LeanInit___instance__17___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Init_LeanInit___instance__17(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_string_utf8_extract(x_2, x_3, x_4);
x_6 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_7 = l_Lean_mkStxStrLit(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_mkOptionalNode___closed__2;
x_9 = lean_array_push(x_8, x_7);
x_10 = l_Lean_Init_LeanInit___instance__17___closed__4;
x_11 = l_Lean_mkCAppStx(x_10, x_9);
return x_11;
}
}
lean_object* l_Lean_Init_LeanInit___instance__17___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Init_LeanInit___instance__17(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_3(x_3, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_3(x_4, x_12, x_13, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_quoteName_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l___private_Init_LeanInit_0__Lean_quoteName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymous");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_LeanInit_0__Lean_quoteName___closed__2;
x_2 = l___private_Init_LeanInit_0__Lean_quoteName___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_LeanInit_0__Lean_quoteName___closed__4;
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkNameStr");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l___private_Init_LeanInit_0__Lean_quoteName___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkNameNum");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l___private_Init_LeanInit_0__Lean_quoteName___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteName(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_0__Lean_quoteName___closed__5;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Init_LeanInit_0__Lean_quoteName(x_3);
x_6 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_7 = l_Lean_mkStxStrLit(x_4, x_6);
lean_dec(x_4);
x_8 = l_Lean_mkAppStx___closed__9;
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_array_push(x_9, x_7);
x_11 = l___private_Init_LeanInit_0__Lean_quoteName___closed__7;
x_12 = l_Lean_mkCAppStx(x_11, x_10);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l___private_Init_LeanInit_0__Lean_quoteName(x_13);
x_16 = l_Nat_repr(x_14);
x_17 = l_Lean_numLitKind;
x_18 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_19 = l_Lean_mkStxLit(x_17, x_16, x_18);
x_20 = l_Lean_mkAppStx___closed__9;
x_21 = lean_array_push(x_20, x_15);
x_22 = lean_array_push(x_21, x_19);
x_23 = l___private_Init_LeanInit_0__Lean_quoteName___closed__9;
x_24 = l_Lean_mkCAppStx(x_23, x_22);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__18___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_quoteName), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__18() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Init_LeanInit___instance__18___closed__1;
return x_1;
}
}
lean_object* l_Lean_Init_LeanInit___instance__19_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Init_LeanInit___instance__19_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Init_LeanInit___instance__19_match__1___rarg), 2, 0);
return x_4;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__19___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Prod");
return x_1;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__19___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Init_LeanInit___instance__19___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__19___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mk");
return x_1;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__19___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__19___rarg___closed__2;
x_2 = l_Lean_Init_LeanInit___instance__19___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Init_LeanInit___instance__19___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = l_Lean_mkAppStx___closed__9;
x_9 = lean_array_push(x_8, x_6);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_Init_LeanInit___instance__19___rarg___closed__4;
x_12 = l_Lean_mkCAppStx(x_11, x_10);
return x_12;
}
}
lean_object* l_Lean_Init_LeanInit___instance__19(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Init_LeanInit___instance__19___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteList_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteList_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_quoteList_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("List");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nil");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__2;
x_2 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__4;
x_3 = l_Lean_mkCIdentFrom(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cons");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__2;
x_2 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__5;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = lean_apply_1(x_1, x_4);
x_7 = l___private_Init_LeanInit_0__Lean_quoteList___rarg(x_1, x_5);
x_8 = l_Lean_mkAppStx___closed__9;
x_9 = lean_array_push(x_8, x_6);
x_10 = lean_array_push(x_9, x_7);
x_11 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__7;
x_12 = l_Lean_mkCAppStx(x_11, x_10);
return x_12;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_quoteList___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Init_LeanInit___instance__20___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_quoteList___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Init_LeanInit___instance__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Init_LeanInit___instance__20___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toArray");
return x_1;
}
}
static lean_object* _init_l_Lean_Init_LeanInit___instance__21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__2;
x_2 = l_Lean_Init_LeanInit___instance__21___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Init_LeanInit___instance__21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Array_toList___rarg(x_2);
x_4 = l___private_Init_LeanInit_0__Lean_quoteList___rarg(x_1, x_3);
x_5 = l_Lean_mkOptionalNode___closed__2;
x_6 = lean_array_push(x_5, x_4);
x_7 = l_Lean_Init_LeanInit___instance__21___rarg___closed__2;
x_8 = l_Lean_mkCAppStx(x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Init_LeanInit___instance__21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Init_LeanInit___instance__21___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Init_LeanInit___instance__21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Init_LeanInit___instance__21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_quoteOption_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Option");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__2;
x_2 = l_Init_Data_Repr___instance__9___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__3;
x_2 = lean_mk_syntax_ident(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("some");
return x_1;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__2;
x_2 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__4;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = l_Lean_mkOptionalNode___closed__2;
x_7 = lean_array_push(x_6, x_5);
x_8 = l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__6;
x_9 = l_Lean_mkCAppStx(x_8, x_7);
return x_9;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_quoteOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_quoteOption___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Option_hasQuote___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_quoteOption___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Option_hasQuote(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Option_hasQuote___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___at_Array_getSepElems___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set(x_4, 0, x_15);
x_3 = x_9;
goto _start;
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
x_3 = x_9;
x_4 = x_20;
goto _start;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = lean_array_push(x_23, x_7);
x_26 = 0;
x_27 = lean_box(x_26);
lean_ctor_set(x_4, 1, x_25);
lean_ctor_set(x_4, 0, x_27);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_array_push(x_29, x_7);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_3 = x_9;
x_4 = x_33;
goto _start;
}
}
}
}
}
lean_object* l_Array_iterateMAux___at_Array_getSepElems___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___at_Array_getSepElems___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_getSepElems___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_getEvenElems___rarg___closed__1;
x_4 = l_Array_iterateMAux___at_Array_getSepElems___spec__1___rarg(x_1, x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Array_getSepElems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_getSepElems___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___at_Array_getSepElems___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___at_Array_getSepElems___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_getSepElems___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_getSepElems___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_add(x_1, x_8);
lean_dec(x_1);
x_10 = l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg(x_2, x_3, x_4, x_9, x_5);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_5);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_1);
x_14 = lean_nat_sub(x_1, lean_box(1));
x_15 = lean_array_fget(x_3, x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_add(x_1, x_16);
lean_dec(x_1);
x_18 = lean_array_push(x_5, x_15);
x_19 = lean_array_push(x_18, x_6);
x_20 = l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg(x_2, x_3, x_4, x_17, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_add(x_1, x_21);
lean_dec(x_1);
x_23 = lean_array_push(x_5, x_6);
x_24 = l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg(x_2, x_3, x_4, x_22, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_add(x_1, x_25);
lean_dec(x_1);
x_27 = lean_array_push(x_5, x_6);
x_28 = l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg(x_2, x_3, x_4, x_26, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_2, x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_11);
x_13 = lean_apply_1(x_3, x_11);
x_14 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_3);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_11);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
lean_object* l_Array_filterSepElemsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Init_LeanInit_0__Array_filterSepElemsMAux___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_filterSepElemsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_filterSepElemsM___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_1, x_3);
lean_inc(x_2);
lean_inc(x_7);
x_8 = lean_apply_1(x_2, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = l_Array_isEmpty___rarg(x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_3);
x_16 = lean_nat_sub(x_3, lean_box(1));
x_17 = lean_array_fget(x_1, x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_20 = lean_array_push(x_4, x_17);
x_21 = lean_array_push(x_20, x_7);
x_3 = x_19;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
x_25 = lean_array_push(x_4, x_7);
x_3 = x_24;
x_4 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_nat_add(x_3, x_27);
lean_dec(x_3);
x_29 = lean_array_push(x_4, x_7);
x_3 = x_28;
x_4 = x_29;
goto _start;
}
}
}
}
}
lean_object* l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_empty___closed__1;
x_5 = l___private_Init_LeanInit_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_filterSepElems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_LeanInit_0__Array_filterSepElemsMAux___at_Array_filterSepElems___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_filterSepElemsM___at_Array_filterSepElems___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_filterSepElems___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_filterSepElems(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = lean_array_push(x_2, x_6);
x_10 = l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_fget(x_2, x_4);
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
x_18 = lean_array_push(x_5, x_11);
x_4 = x_17;
x_5 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_3);
x_21 = lean_apply_1(x_3, x_11);
x_22 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_2);
lean_closure_set(x_22, 4, x_3);
x_23 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapSepElemsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Init_LeanInit_0__Array_mapSepElemsMAux___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_mapSepElemsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapSepElemsM___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_fget(x_1, x_3);
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
x_14 = lean_array_push(x_4, x_7);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_2);
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
lean_object* l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_empty___closed__1;
x_5 = l___private_Init_LeanInit_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_mapSepElems(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_LeanInit_0__Array_mapSepElemsMAux___at_Array_mapSepElems___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapSepElemsM___at_Array_mapSepElems___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mapSepElems___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapSepElems(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 123;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_decodeQuotedChar(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = lean_string_utf8_next(x_1, x_2);
x_6 = 123;
x_7 = x_4 == x_6;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_4 = lean_string_utf8_get(x_1, x_2);
x_5 = lean_string_utf8_next(x_1, x_2);
lean_dec(x_2);
x_6 = 34;
x_7 = x_4 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 123;
x_9 = x_4 == x_8;
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_string_utf8_at_end(x_1, x_5);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 92;
x_12 = x_4 == x_11;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_string_push(x_3, x_4);
x_2 = x_5;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unbox_uint32(x_18);
lean_dec(x_18);
x_21 = lean_string_push(x_3, x_20);
x_2 = x_19;
x_3 = x_21;
goto _start;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_3);
x_23 = lean_box(0);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_3);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_3);
return x_25;
}
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_String_splitAux___closed__1;
x_4 = l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_isInterpolatedStrLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_interpolatedStrLitKind;
x_3 = l_Lean_Syntax_isLit_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_String_splitAux___closed__1;
x_8 = l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrLit_loop(x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
}
lean_object* l_Lean_Syntax_isInterpolatedStrLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_isInterpolatedStrLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_expandInterpolatedStrChunks_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_expandInterpolatedStrChunks_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_expandInterpolatedStrChunks_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_5);
x_10 = lean_apply_4(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_apply_5(x_7, x_2, x_11, x_13, x_5, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_2);
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
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_apply_5(x_7, x_2, x_4, x_19, x_5, x_6);
return x_20;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_5 < x_4;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_5);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_Syntax_isInterpolatedStrLit_x3f(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_inc(x_2);
lean_inc(x_7);
x_15 = lean_apply_3(x_2, x_11, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_1);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2(x_1, x_12, x_13, x_16, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = 1;
x_29 = x_5 + x_28;
x_5 = x_29;
x_6 = x_27;
x_8 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_11);
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
lean_dec(x_14);
x_40 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_41 = l_Lean_mkStxStrLit(x_39, x_40);
lean_dec(x_39);
lean_inc(x_2);
lean_inc(x_7);
x_42 = lean_apply_3(x_2, x_41, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_7);
lean_inc(x_1);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2(x_1, x_12, x_13, x_43, x_7, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
lean_dec(x_46);
x_55 = 1;
x_56 = x_5 + x_55;
x_5 = x_56;
x_6 = x_54;
x_8 = x_53;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
return x_42;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_42, 0);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_42);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_expandInterpolatedStrChunks___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Lean_Syntax_expandInterpolatedStrChunks___closed__1;
x_10 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1(x_2, x_3, x_1, x_7, x_8, x_9, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Syntax_expandInterpolatedStrChunks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_expandInterpolatedStrChunks(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___at_Lean_Syntax_getSepArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set(x_4, 0, x_15);
x_3 = x_9;
goto _start;
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
x_3 = x_9;
x_4 = x_20;
goto _start;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = lean_array_push(x_23, x_7);
x_26 = 0;
x_27 = lean_box(x_26);
lean_ctor_set(x_4, 1, x_25);
lean_ctor_set(x_4, 0, x_27);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_array_push(x_29, x_7);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_3 = x_9;
x_4 = x_33;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Syntax_getSepArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Syntax_getArgs(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_getEvenElems___rarg___closed__1;
x_5 = l_Array_iterateMAux___at_Lean_Syntax_getSepArgs___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Array_iterateMAux___at_Lean_Syntax_getSepArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___at_Lean_Syntax_getSepArgs___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_getSepArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_getSepArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Option_BasicAux(lean_object*);
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
lean_object* initialize_Init_Data_Array_ForIn(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Hashable(lean_object*);
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Control_EState(lean_object*);
lean_object* initialize_Init_Control_StateRef(lean_object*);
lean_object* initialize_Init_Control_Option(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_LeanInit(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_BasicAux(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_ForIn(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_EState(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_idBeginEscape = _init_l_Lean_idBeginEscape();
l_Lean_idEndEscape = _init_l_Lean_idEndEscape();
l_Lean_Init_LeanInit___instance__1 = _init_l_Lean_Init_LeanInit___instance__1();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__1);
l_Lean_Init_LeanInit___instance__2___closed__1 = _init_l_Lean_Init_LeanInit___instance__2___closed__1();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__2___closed__1);
l_Lean_Init_LeanInit___instance__2 = _init_l_Lean_Init_LeanInit___instance__2();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__2);
l_Lean_Name_Init_LeanInit___instance__3___closed__1 = _init_l_Lean_Name_Init_LeanInit___instance__3___closed__1();
lean_mark_persistent(l_Lean_Name_Init_LeanInit___instance__3___closed__1);
l_Lean_Name_Init_LeanInit___instance__3 = _init_l_Lean_Name_Init_LeanInit___instance__3();
lean_mark_persistent(l_Lean_Name_Init_LeanInit___instance__3);
l_Lean_Name_toStringWithSep___closed__1 = _init_l_Lean_Name_toStringWithSep___closed__1();
lean_mark_persistent(l_Lean_Name_toStringWithSep___closed__1);
l_Lean_Name_Init_LeanInit___instance__4___closed__1 = _init_l_Lean_Name_Init_LeanInit___instance__4___closed__1();
lean_mark_persistent(l_Lean_Name_Init_LeanInit___instance__4___closed__1);
l_Lean_Name_Init_LeanInit___instance__4 = _init_l_Lean_Name_Init_LeanInit___instance__4();
lean_mark_persistent(l_Lean_Name_Init_LeanInit___instance__4);
l_Lean_Name_Init_LeanInit___instance__5___closed__1 = _init_l_Lean_Name_Init_LeanInit___instance__5___closed__1();
lean_mark_persistent(l_Lean_Name_Init_LeanInit___instance__5___closed__1);
l_Lean_Name_Init_LeanInit___instance__5 = _init_l_Lean_Name_Init_LeanInit___instance__5();
lean_mark_persistent(l_Lean_Name_Init_LeanInit___instance__5);
l_Lean_Name_appendIndexAfter___closed__1 = _init_l_Lean_Name_appendIndexAfter___closed__1();
lean_mark_persistent(l_Lean_Name_appendIndexAfter___closed__1);
l_Lean_NameGenerator_namePrefix___default___closed__1 = _init_l_Lean_NameGenerator_namePrefix___default___closed__1();
lean_mark_persistent(l_Lean_NameGenerator_namePrefix___default___closed__1);
l_Lean_NameGenerator_namePrefix___default___closed__2 = _init_l_Lean_NameGenerator_namePrefix___default___closed__2();
lean_mark_persistent(l_Lean_NameGenerator_namePrefix___default___closed__2);
l_Lean_NameGenerator_namePrefix___default = _init_l_Lean_NameGenerator_namePrefix___default();
lean_mark_persistent(l_Lean_NameGenerator_namePrefix___default);
l_Lean_NameGenerator_idx___default = _init_l_Lean_NameGenerator_idx___default();
lean_mark_persistent(l_Lean_NameGenerator_idx___default);
l_Lean_NameGenerator_Init_LeanInit___instance__6___closed__1 = _init_l_Lean_NameGenerator_Init_LeanInit___instance__6___closed__1();
lean_mark_persistent(l_Lean_NameGenerator_Init_LeanInit___instance__6___closed__1);
l_Lean_NameGenerator_Init_LeanInit___instance__6 = _init_l_Lean_NameGenerator_Init_LeanInit___instance__6();
lean_mark_persistent(l_Lean_NameGenerator_Init_LeanInit___instance__6);
l_Lean_Init_LeanInit___instance__7___closed__1 = _init_l_Lean_Init_LeanInit___instance__7___closed__1();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__7___closed__1);
l_Lean_Init_LeanInit___instance__7 = _init_l_Lean_Init_LeanInit___instance__7();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__7);
l_Lean_SourceInfo_leading___default = _init_l_Lean_SourceInfo_leading___default();
lean_mark_persistent(l_Lean_SourceInfo_leading___default);
l_Lean_SourceInfo_pos___default = _init_l_Lean_SourceInfo_pos___default();
lean_mark_persistent(l_Lean_SourceInfo_pos___default);
l_Lean_SourceInfo_trailing___default = _init_l_Lean_SourceInfo_trailing___default();
lean_mark_persistent(l_Lean_SourceInfo_trailing___default);
l_Lean_Init_LeanInit___instance__8___closed__1 = _init_l_Lean_Init_LeanInit___instance__8___closed__1();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__8___closed__1);
l_Lean_Init_LeanInit___instance__8 = _init_l_Lean_Init_LeanInit___instance__8();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__8);
l_Lean_Init_LeanInit___instance__9 = _init_l_Lean_Init_LeanInit___instance__9();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__9);
l_Lean_choiceKind___closed__1 = _init_l_Lean_choiceKind___closed__1();
lean_mark_persistent(l_Lean_choiceKind___closed__1);
l_Lean_choiceKind___closed__2 = _init_l_Lean_choiceKind___closed__2();
lean_mark_persistent(l_Lean_choiceKind___closed__2);
l_Lean_choiceKind = _init_l_Lean_choiceKind();
lean_mark_persistent(l_Lean_choiceKind);
l_Lean_nullKind___closed__1 = _init_l_Lean_nullKind___closed__1();
lean_mark_persistent(l_Lean_nullKind___closed__1);
l_Lean_nullKind___closed__2 = _init_l_Lean_nullKind___closed__2();
lean_mark_persistent(l_Lean_nullKind___closed__2);
l_Lean_nullKind = _init_l_Lean_nullKind();
lean_mark_persistent(l_Lean_nullKind);
l_Lean_identKind___closed__1 = _init_l_Lean_identKind___closed__1();
lean_mark_persistent(l_Lean_identKind___closed__1);
l_Lean_identKind___closed__2 = _init_l_Lean_identKind___closed__2();
lean_mark_persistent(l_Lean_identKind___closed__2);
l_Lean_identKind = _init_l_Lean_identKind();
lean_mark_persistent(l_Lean_identKind);
l_Lean_strLitKind___closed__1 = _init_l_Lean_strLitKind___closed__1();
lean_mark_persistent(l_Lean_strLitKind___closed__1);
l_Lean_strLitKind___closed__2 = _init_l_Lean_strLitKind___closed__2();
lean_mark_persistent(l_Lean_strLitKind___closed__2);
l_Lean_strLitKind = _init_l_Lean_strLitKind();
lean_mark_persistent(l_Lean_strLitKind);
l_Lean_charLitKind___closed__1 = _init_l_Lean_charLitKind___closed__1();
lean_mark_persistent(l_Lean_charLitKind___closed__1);
l_Lean_charLitKind___closed__2 = _init_l_Lean_charLitKind___closed__2();
lean_mark_persistent(l_Lean_charLitKind___closed__2);
l_Lean_charLitKind = _init_l_Lean_charLitKind();
lean_mark_persistent(l_Lean_charLitKind);
l_Lean_numLitKind___closed__1 = _init_l_Lean_numLitKind___closed__1();
lean_mark_persistent(l_Lean_numLitKind___closed__1);
l_Lean_numLitKind___closed__2 = _init_l_Lean_numLitKind___closed__2();
lean_mark_persistent(l_Lean_numLitKind___closed__2);
l_Lean_numLitKind = _init_l_Lean_numLitKind();
lean_mark_persistent(l_Lean_numLitKind);
l_Lean_nameLitKind___closed__1 = _init_l_Lean_nameLitKind___closed__1();
lean_mark_persistent(l_Lean_nameLitKind___closed__1);
l_Lean_nameLitKind___closed__2 = _init_l_Lean_nameLitKind___closed__2();
lean_mark_persistent(l_Lean_nameLitKind___closed__2);
l_Lean_nameLitKind = _init_l_Lean_nameLitKind();
lean_mark_persistent(l_Lean_nameLitKind);
l_Lean_fieldIdxKind___closed__1 = _init_l_Lean_fieldIdxKind___closed__1();
lean_mark_persistent(l_Lean_fieldIdxKind___closed__1);
l_Lean_fieldIdxKind___closed__2 = _init_l_Lean_fieldIdxKind___closed__2();
lean_mark_persistent(l_Lean_fieldIdxKind___closed__2);
l_Lean_fieldIdxKind = _init_l_Lean_fieldIdxKind();
lean_mark_persistent(l_Lean_fieldIdxKind);
l_Lean_interpolatedStrLitKind___closed__1 = _init_l_Lean_interpolatedStrLitKind___closed__1();
lean_mark_persistent(l_Lean_interpolatedStrLitKind___closed__1);
l_Lean_interpolatedStrLitKind___closed__2 = _init_l_Lean_interpolatedStrLitKind___closed__2();
lean_mark_persistent(l_Lean_interpolatedStrLitKind___closed__2);
l_Lean_interpolatedStrLitKind = _init_l_Lean_interpolatedStrLitKind();
lean_mark_persistent(l_Lean_interpolatedStrLitKind);
l_Lean_interpolatedStrKind___closed__1 = _init_l_Lean_interpolatedStrKind___closed__1();
lean_mark_persistent(l_Lean_interpolatedStrKind___closed__1);
l_Lean_interpolatedStrKind___closed__2 = _init_l_Lean_interpolatedStrKind___closed__2();
lean_mark_persistent(l_Lean_interpolatedStrKind___closed__2);
l_Lean_interpolatedStrKind = _init_l_Lean_interpolatedStrKind();
lean_mark_persistent(l_Lean_interpolatedStrKind);
l_Lean_Syntax_getKind___closed__1 = _init_l_Lean_Syntax_getKind___closed__1();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__1);
l_Lean_Syntax_getKind___closed__2 = _init_l_Lean_Syntax_getKind___closed__2();
lean_mark_persistent(l_Lean_Syntax_getKind___closed__2);
l_Lean_reservedMacroScope = _init_l_Lean_reservedMacroScope();
lean_mark_persistent(l_Lean_reservedMacroScope);
l_Lean_firstFrontendMacroScope___closed__1 = _init_l_Lean_firstFrontendMacroScope___closed__1();
lean_mark_persistent(l_Lean_firstFrontendMacroScope___closed__1);
l_Lean_firstFrontendMacroScope = _init_l_Lean_firstFrontendMacroScope();
lean_mark_persistent(l_Lean_firstFrontendMacroScope);
l_Lean_Name_hasMacroScopes___closed__1 = _init_l_Lean_Name_hasMacroScopes___closed__1();
lean_mark_persistent(l_Lean_Name_hasMacroScopes___closed__1);
l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__1 = _init_l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__1);
l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__2 = _init_l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__2();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__2);
l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3 = _init_l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3);
l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__4 = _init_l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__4();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__4);
l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5 = _init_l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__5);
l_Lean_Init_LeanInit___instance__10___closed__1 = _init_l_Lean_Init_LeanInit___instance__10___closed__1();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__10___closed__1);
l_Lean_Init_LeanInit___instance__10 = _init_l_Lean_Init_LeanInit___instance__10();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__10);
l___private_Init_LeanInit_0__Lean_assembleParts___closed__1 = _init_l___private_Init_LeanInit_0__Lean_assembleParts___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_assembleParts___closed__1);
l___private_Init_LeanInit_0__Lean_assembleParts___closed__2 = _init_l___private_Init_LeanInit_0__Lean_assembleParts___closed__2();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_assembleParts___closed__2);
l___private_Init_LeanInit_0__Lean_extractImported___closed__1 = _init_l___private_Init_LeanInit_0__Lean_extractImported___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_extractImported___closed__1);
l___private_Init_LeanInit_0__Lean_extractImported___closed__2 = _init_l___private_Init_LeanInit_0__Lean_extractImported___closed__2();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_extractImported___closed__2);
l___private_Init_LeanInit_0__Lean_extractMainModule___closed__1 = _init_l___private_Init_LeanInit_0__Lean_extractMainModule___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_extractMainModule___closed__1);
l___private_Init_LeanInit_0__Lean_extractMainModule___closed__2 = _init_l___private_Init_LeanInit_0__Lean_extractMainModule___closed__2();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_extractMainModule___closed__2);
l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__1 = _init_l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__1);
l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__2 = _init_l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__2();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_extractMacroScopesAux___closed__2);
l_Lean_defaultMaxRecDepth = _init_l_Lean_defaultMaxRecDepth();
lean_mark_persistent(l_Lean_defaultMaxRecDepth);
l_Lean_maxRecDepthErrorMessage___closed__1 = _init_l_Lean_maxRecDepthErrorMessage___closed__1();
lean_mark_persistent(l_Lean_maxRecDepthErrorMessage___closed__1);
l_Lean_maxRecDepthErrorMessage = _init_l_Lean_maxRecDepthErrorMessage();
lean_mark_persistent(l_Lean_maxRecDepthErrorMessage);
l_Lean_Macro_MacroEnvPointed = _init_l_Lean_Macro_MacroEnvPointed();
lean_mark_persistent(l_Lean_Macro_MacroEnvPointed);
l_Lean_Macro_Init_LeanInit___instance__11 = _init_l_Lean_Macro_Init_LeanInit___instance__11();
lean_mark_persistent(l_Lean_Macro_Init_LeanInit___instance__11);
l_Lean_Macro_Context_currRecDepth___default = _init_l_Lean_Macro_Context_currRecDepth___default();
lean_mark_persistent(l_Lean_Macro_Context_currRecDepth___default);
l_Lean_Macro_Context_maxRecDepth___default = _init_l_Lean_Macro_Context_maxRecDepth___default();
lean_mark_persistent(l_Lean_Macro_Context_maxRecDepth___default);
l_Lean_Macro_Init_LeanInit___instance__12___closed__1 = _init_l_Lean_Macro_Init_LeanInit___instance__12___closed__1();
lean_mark_persistent(l_Lean_Macro_Init_LeanInit___instance__12___closed__1);
l_Lean_Macro_Init_LeanInit___instance__12___closed__2 = _init_l_Lean_Macro_Init_LeanInit___instance__12___closed__2();
lean_mark_persistent(l_Lean_Macro_Init_LeanInit___instance__12___closed__2);
l_Lean_Macro_Init_LeanInit___instance__12___closed__3 = _init_l_Lean_Macro_Init_LeanInit___instance__12___closed__3();
lean_mark_persistent(l_Lean_Macro_Init_LeanInit___instance__12___closed__3);
l_Lean_Macro_Init_LeanInit___instance__12___closed__4 = _init_l_Lean_Macro_Init_LeanInit___instance__12___closed__4();
lean_mark_persistent(l_Lean_Macro_Init_LeanInit___instance__12___closed__4);
l_Lean_Macro_Init_LeanInit___instance__12 = _init_l_Lean_Macro_Init_LeanInit___instance__12();
lean_mark_persistent(l_Lean_Macro_Init_LeanInit___instance__12);
l_Lean_Macro_expandMacroNotAvailable_x3f___closed__1 = _init_l_Lean_Macro_expandMacroNotAvailable_x3f___closed__1();
lean_mark_persistent(l_Lean_Macro_expandMacroNotAvailable_x3f___closed__1);
l_Lean_Macro_mkMacroEnvSimple___closed__1 = _init_l_Lean_Macro_mkMacroEnvSimple___closed__1();
lean_mark_persistent(l_Lean_Macro_mkMacroEnvSimple___closed__1);
l_Lean_Macro_mkMacroEnvSimple___closed__2 = _init_l_Lean_Macro_mkMacroEnvSimple___closed__2();
lean_mark_persistent(l_Lean_Macro_mkMacroEnvSimple___closed__2);
l_Lean_Macro_mkMacroEnvSimple = _init_l_Lean_Macro_mkMacroEnvSimple();
lean_mark_persistent(l_Lean_Macro_mkMacroEnvSimple);
l_Lean_mkCIdentFrom___closed__1 = _init_l_Lean_mkCIdentFrom___closed__1();
lean_mark_persistent(l_Lean_mkCIdentFrom___closed__1);
l_Lean_mkCIdentFrom___closed__2 = _init_l_Lean_mkCIdentFrom___closed__2();
lean_mark_persistent(l_Lean_mkCIdentFrom___closed__2);
l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_mkSepArray___spec__1___closed__1);
l_Lean_mkSepArray___closed__1 = _init_l_Lean_mkSepArray___closed__1();
lean_mark_persistent(l_Lean_mkSepArray___closed__1);
l_Lean_mkOptionalNode___closed__1 = _init_l_Lean_mkOptionalNode___closed__1();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__1);
l_Lean_mkOptionalNode___closed__2 = _init_l_Lean_mkOptionalNode___closed__2();
lean_mark_persistent(l_Lean_mkOptionalNode___closed__2);
l_Lean_mkAppStx___closed__1 = _init_l_Lean_mkAppStx___closed__1();
lean_mark_persistent(l_Lean_mkAppStx___closed__1);
l_Lean_mkAppStx___closed__2 = _init_l_Lean_mkAppStx___closed__2();
lean_mark_persistent(l_Lean_mkAppStx___closed__2);
l_Lean_mkAppStx___closed__3 = _init_l_Lean_mkAppStx___closed__3();
lean_mark_persistent(l_Lean_mkAppStx___closed__3);
l_Lean_mkAppStx___closed__4 = _init_l_Lean_mkAppStx___closed__4();
lean_mark_persistent(l_Lean_mkAppStx___closed__4);
l_Lean_mkAppStx___closed__5 = _init_l_Lean_mkAppStx___closed__5();
lean_mark_persistent(l_Lean_mkAppStx___closed__5);
l_Lean_mkAppStx___closed__6 = _init_l_Lean_mkAppStx___closed__6();
lean_mark_persistent(l_Lean_mkAppStx___closed__6);
l_Lean_mkAppStx___closed__7 = _init_l_Lean_mkAppStx___closed__7();
lean_mark_persistent(l_Lean_mkAppStx___closed__7);
l_Lean_mkAppStx___closed__8 = _init_l_Lean_mkAppStx___closed__8();
lean_mark_persistent(l_Lean_mkAppStx___closed__8);
l_Lean_mkAppStx___closed__9 = _init_l_Lean_mkAppStx___closed__9();
lean_mark_persistent(l_Lean_mkAppStx___closed__9);
l_Lean_mkHole___closed__1 = _init_l_Lean_mkHole___closed__1();
lean_mark_persistent(l_Lean_mkHole___closed__1);
l_Lean_mkHole___closed__2 = _init_l_Lean_mkHole___closed__2();
lean_mark_persistent(l_Lean_mkHole___closed__2);
l_Lean_Syntax_decodeNatLitVal___closed__1 = _init_l_Lean_Syntax_decodeNatLitVal___closed__1();
lean_mark_persistent(l_Lean_Syntax_decodeNatLitVal___closed__1);
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
l_Lean_Init_LeanInit___instance__14 = _init_l_Lean_Init_LeanInit___instance__14();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__14);
l_Lean_Init_LeanInit___instance__17___closed__1 = _init_l_Lean_Init_LeanInit___instance__17___closed__1();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__17___closed__1);
l_Lean_Init_LeanInit___instance__17___closed__2 = _init_l_Lean_Init_LeanInit___instance__17___closed__2();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__17___closed__2);
l_Lean_Init_LeanInit___instance__17___closed__3 = _init_l_Lean_Init_LeanInit___instance__17___closed__3();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__17___closed__3);
l_Lean_Init_LeanInit___instance__17___closed__4 = _init_l_Lean_Init_LeanInit___instance__17___closed__4();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__17___closed__4);
l___private_Init_LeanInit_0__Lean_quoteName___closed__1 = _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteName___closed__1);
l___private_Init_LeanInit_0__Lean_quoteName___closed__2 = _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__2();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteName___closed__2);
l___private_Init_LeanInit_0__Lean_quoteName___closed__3 = _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__3();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteName___closed__3);
l___private_Init_LeanInit_0__Lean_quoteName___closed__4 = _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__4();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteName___closed__4);
l___private_Init_LeanInit_0__Lean_quoteName___closed__5 = _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__5();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteName___closed__5);
l___private_Init_LeanInit_0__Lean_quoteName___closed__6 = _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__6();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteName___closed__6);
l___private_Init_LeanInit_0__Lean_quoteName___closed__7 = _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__7();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteName___closed__7);
l___private_Init_LeanInit_0__Lean_quoteName___closed__8 = _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__8();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteName___closed__8);
l___private_Init_LeanInit_0__Lean_quoteName___closed__9 = _init_l___private_Init_LeanInit_0__Lean_quoteName___closed__9();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteName___closed__9);
l_Lean_Init_LeanInit___instance__18___closed__1 = _init_l_Lean_Init_LeanInit___instance__18___closed__1();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__18___closed__1);
l_Lean_Init_LeanInit___instance__18 = _init_l_Lean_Init_LeanInit___instance__18();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__18);
l_Lean_Init_LeanInit___instance__19___rarg___closed__1 = _init_l_Lean_Init_LeanInit___instance__19___rarg___closed__1();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__19___rarg___closed__1);
l_Lean_Init_LeanInit___instance__19___rarg___closed__2 = _init_l_Lean_Init_LeanInit___instance__19___rarg___closed__2();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__19___rarg___closed__2);
l_Lean_Init_LeanInit___instance__19___rarg___closed__3 = _init_l_Lean_Init_LeanInit___instance__19___rarg___closed__3();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__19___rarg___closed__3);
l_Lean_Init_LeanInit___instance__19___rarg___closed__4 = _init_l_Lean_Init_LeanInit___instance__19___rarg___closed__4();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__19___rarg___closed__4);
l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__1 = _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__1);
l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__2 = _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__2();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__2);
l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__3 = _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__3();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__3);
l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__4 = _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__4();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__4);
l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__5 = _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__5();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__5);
l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__6 = _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__6();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__6);
l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__7 = _init_l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__7();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteList___rarg___closed__7);
l_Lean_Init_LeanInit___instance__21___rarg___closed__1 = _init_l_Lean_Init_LeanInit___instance__21___rarg___closed__1();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__21___rarg___closed__1);
l_Lean_Init_LeanInit___instance__21___rarg___closed__2 = _init_l_Lean_Init_LeanInit___instance__21___rarg___closed__2();
lean_mark_persistent(l_Lean_Init_LeanInit___instance__21___rarg___closed__2);
l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__1 = _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__1();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__1);
l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__2 = _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__2();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__2);
l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__3 = _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__3();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__3);
l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__4 = _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__4();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__4);
l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__5 = _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__5();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__5);
l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__6 = _init_l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__6();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_quoteOption___rarg___closed__6);
l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1 = _init_l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1();
lean_mark_persistent(l___private_Init_LeanInit_0__Lean_Syntax_decodeInterpStrQuotedChar___boxed__const__1);
l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Syntax_expandInterpolatedStrChunks___spec__1___lambda__2___closed__1);
l_Lean_Syntax_expandInterpolatedStrChunks___closed__1 = _init_l_Lean_Syntax_expandInterpolatedStrChunks___closed__1();
lean_mark_persistent(l_Lean_Syntax_expandInterpolatedStrChunks___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
