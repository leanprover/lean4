// Lean compiler output
// Module: Lean.Data.Xml.Parser
// Imports: Init Lean.Data.Parsec Lean.Data.Xml.Basic
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
static lean_object* l_Lean_Xml_Parser_cp___closed__3;
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__12;
static lean_object* l_Lean_Xml_Parser_CDStart___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_Char___closed__3;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NameChar___boxed__const__1;
static lean_object* l_Lean_Xml_Parser_NameChar___closed__8;
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PI___lambda__1(lean_object*);
static lean_object* l_Lean_Xml_Parser_doctypedecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttValue___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_elementDecl(lean_object*);
static lean_object* l_Lean_Xml_Parser_NameChar___closed__11;
static lean_object* l_Lean_Xml_Parser_AttValue___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Xml_Parser_Mixed___lambda__1___closed__3;
static lean_object* l_Lean_Xml_Parser_SDDecl___closed__1;
static lean_object* l_Lean_Xml_Parser_NameStartChar___closed__3;
extern lean_object* l_Lean_Parsec_expectedEndOfInput;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PubidLiteral___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_PubidLiteral___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_digitsToNat___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Xml_Parser_VersionNum___closed__1;
static lean_object* l_Lean_Xml_Parser_DefaultDecl___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Xml_Parser_VersionInfo___closed__1;
static lean_object* l_Lean_Xml_parse___closed__1;
static lean_object* l_Lean_Xml_Parser_contentspec___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CharData___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityValue___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PubidLiteral___lambda__1(uint32_t, lean_object*);
static lean_object* l_Lean_Xml_Parser_contentspec___closed__1;
static lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__2;
static lean_object* l_Lean_Xml_Parser_endl___closed__6;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__6;
static lean_object* l_Lean_Xml_Parser_VersionNum___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_predefinedEntityToChar(lean_object*);
static lean_object* l_Lean_Xml_parse___closed__2;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__3;
static lean_object* l_Lean_Xml_Parser_Mixed___closed__6;
static lean_object* l_Lean_Xml_Parser_CharRef___closed__3;
static lean_object* l_Lean_Xml_Parser_intSubset___closed__1;
lean_object* l_Lean_Parsec_many1Chars(lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_seq___lambda__1___closed__3;
static lean_object* l_Lean_Xml_Parser_doctypedecl___closed__4;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_elementDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__2;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__3;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PEDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__10___boxed__const__1;
lean_object* l_Lean_Parsec_manyChars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CharData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EncodingDecl(lean_object*);
static lean_object* l_Lean_Xml_Parser_PITarget___closed__5;
static lean_object* l_Lean_Xml_Parser_Mixed___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Xml_Parser_content___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__3;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__5;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_digitsToNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_document(lean_object*);
static lean_object* l_Lean_Xml_Parser_elementDecl___closed__2;
static lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__3;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttValue___closed__2___boxed__const__1;
static lean_object* l_Lean_Xml_Parser_cp___closed__7;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__15;
static lean_object* l_Lean_Xml_Parser_CharData___closed__2;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__18;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_choice___lambda__1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_Mixed___closed__5;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_VersionInfo(lean_object*);
static lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__9;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Misc(lean_object*);
static lean_object* l_Lean_Xml_Parser_SDDecl___closed__2;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__4;
lean_object* l_Lean_Parsec_satisfy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PubidLiteral___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityRef(lean_object*);
LEAN_EXPORT lean_object* l_Array_back___at_Lean_Xml_Parser_content___spec__1___boxed(lean_object*);
static lean_object* l_Lean_Xml_Parser_AttlistDecl___closed__2;
static lean_object* l_Lean_Xml_Parser_CharData___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_elementPrefix___lambda__1(lean_object*);
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__14;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityValue___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttlistDecl(lean_object*);
static lean_object* l_Lean_Xml_Parser_PITarget___closed__18;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__15;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CDEnd(lean_object*);
lean_object* l_Lean_Parsec_digit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_ExternalID(lean_object*);
static lean_object* l_Lean_Xml_Parser_NameChar___closed__9;
static lean_object* l_Lean_Xml_Parser_EncodingDecl___closed__2;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__14;
static lean_object* l_Lean_Xml_Parser_elementPrefix___closed__2;
static lean_object* l_Lean_Xml_Parser_PI___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_DeclSep(lean_object*);
lean_object* l_Lean_Parsec_many(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttDef(lean_object*);
static lean_object* l_Lean_Xml_Parser_cp___closed__1;
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l_Lean_Xml_Parser_elementDecl___closed__4;
static lean_object* l_Lean_Xml_Parser_NameChar___closed__4;
static lean_object* l_Lean_Xml_Parser_doctypedecl___closed__5;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_hexDigitToNat(uint32_t);
static lean_object* l_Lean_Xml_Parser_cp___closed__5;
static lean_object* l_Lean_Xml_Parser_elementPrefix___closed__1;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__17;
static lean_object* l_Lean_Xml_Parser_DefaultDecl___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Attribute(lean_object*);
static lean_object* l_Lean_Xml_Parser_endl___closed__4;
static lean_object* l_Lean_Xml_Parser_Mixed___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_parse(lean_object*);
static lean_object* l_Lean_Xml_Parser_CharRef___closed__2;
static lean_object* l_Lean_Xml_Parser_elementDecl___closed__3;
static lean_object* l_Lean_Xml_Parser_EmptyElemTag___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__8___boxed__const__1;
static lean_object* l_Lean_Xml_Parser_cp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Char(lean_object*);
static lean_object* l_Lean_Xml_Parser_DefaultDecl___closed__1;
static lean_object* l_Lean_Xml_Parser_CharRef___closed__1;
static lean_object* l_Lean_Xml_Parser_Eq___closed__3;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EnumeratedType(lean_object*);
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__9;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttValue___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_NameChar___closed__1;
static lean_object* l_Lean_Xml_Parser_Mixed___closed__8;
static lean_object* l_Lean_Xml_Parser_EncName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_intSubset___lambda__1(lean_object*);
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__4;
static lean_object* l_Lean_Xml_Parser_EmptyElemTag___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityValue___closed__2___boxed__const__1;
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
static lean_object* l_Lean_Xml_Parser_Mixed___closed__9;
static lean_object* l_Lean_Xml_Parser_NameChar___closed__2;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_DefaultDecl(lean_object*);
static lean_object* l_Lean_Xml_Parser_PubidChar___closed__2;
static lean_object* l_Lean_Xml_Parser_Mixed___lambda__1___closed__1;
static lean_object* l_Lean_Xml_Parser_content___lambda__1___closed__1;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__17;
static lean_object* l_Lean_Xml_Parser_endl___closed__9;
uint8_t l_instDecidableNot___rarg(uint8_t);
uint8_t l_String_contains(lean_object*, uint32_t);
static lean_object* l_Lean_Xml_Parser_Mixed___closed__4;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__8;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_quote___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_EncName___lambda__1___closed__3;
static lean_object* l_Lean_Xml_Parser_NDataDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_SDDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EncName(lean_object*);
static lean_object* l_Lean_Xml_Parser_doctypedecl___closed__7;
static lean_object* l_Lean_Xml_Parser_elementPrefix___closed__4;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EmptyElemTag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NameStartChar(lean_object*);
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_endl___closed__8;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_endl___boxed__const__1;
static lean_object* l_Lean_Xml_Parser_TokenizedType___closed__4;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_SDDecl___lambda__1(lean_object*);
static lean_object* l_Lean_Xml_Parser_PITarget___closed__9;
static lean_object* l_Lean_Xml_Parser_Mixed___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Xml_Parser_content___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Iterator_extract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_quote(lean_object*);
static lean_object* l_Lean_Xml_Parser_choice___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_S___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EncName___lambda__1(lean_object*);
static lean_object* l_Lean_Xml_Parser_ETag___closed__1;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_digitsToNat___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_markupDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CharRef___lambda__1(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_PubidLiteral___closed__1;
static lean_object* l_Lean_Xml_Parser_VersionInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_intSubset(lean_object*);
static lean_object* l_Lean_Xml_Parser_cp___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_cp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityValue(lean_object*);
static lean_object* l_Lean_Xml_Parser_PubidLiteral___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CharRef(lean_object*);
static lean_object* l_Lean_Xml_Parser_endl___closed__10;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Xml_Parser_Comment___closed__2;
static lean_object* l_Lean_Xml_Parser_EntityRef___closed__5;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_SystemLiteral___closed__3___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_GEDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Mixed___lambda__1(lean_object*);
static lean_object* l_Lean_Xml_Parser_PITarget___closed__13;
static lean_object* l_Lean_Xml_Parser_NameChar___closed__6;
static lean_object* l_Lean_Xml_Parser_elementPrefix___closed__3;
static lean_object* l_Lean_Xml_Parser_Eq___closed__2;
static lean_object* l_Lean_Xml_Parser_TokenizedType___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_AttValue___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Xml_parse___closed__3;
static lean_object* l_Lean_Xml_Parser_Mixed___closed__2;
static lean_object* l_Lean_Xml_Parser_PEReference___closed__1;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__8;
static size_t l_Lean_Xml_Parser_NameStartChar___closed__5;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttValue(lean_object*);
static lean_object* l_Lean_Xml_Parser_Comment___closed__1;
static lean_object* l_Lean_Xml_Parser_EntityRef___closed__3;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_StringType(lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Parsec_attempt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_seq(lean_object*);
static lean_object* l_Lean_Xml_Parser_NotationType___closed__1;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__25;
static lean_object* l_Lean_Xml_Parser_content___closed__2;
static lean_object* l_Lean_Xml_Parser_XMLdecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CDStart(lean_object*);
lean_object* l_Lean_Parsec_pstring(lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_EncName___lambda__1___closed__1;
static lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__7;
lean_object* l_String_Iterator_prevn(lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_EncName___lambda__1___closed__2;
uint8_t l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__1;
static lean_object* l_Lean_Xml_Parser_quote___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PEReference(lean_object*);
static lean_object* l_Lean_Xml_Parser_StringType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityValue___lambda__1(uint32_t, lean_object*);
static lean_object* l_Lean_Xml_Parser_PEReference___closed__2;
lean_object* l_Lean_Parsec_many1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_digitsToNat___boxed(lean_object*, lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
static lean_object* l_Lean_Xml_Parser_XMLdecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_S___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_S(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Mixed(lean_object*);
static lean_object* l_Lean_Xml_Parser_Comment___closed__3;
static lean_object* l_Lean_Xml_Parser_doctypedecl___closed__1;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__22;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Xml_Parser_content___spec__2(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Xml_Parser_AttValue___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__7___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CharRef___lambda__2(lean_object*);
static lean_object* l_Lean_Xml_Parser_GEDecl___closed__1;
static lean_object* l_Lean_Xml_Parser_prolog___closed__1;
static lean_object* l_Lean_Xml_Parser_quote___rarg___closed__2;
uint8_t l_String_Iterator_hasNext(lean_object*);
static lean_object* l_Lean_Xml_Parser_doctypedecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PITarget(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_SystemLiteral(lean_object*);
static lean_object* l_Lean_Xml_Parser_EntityRef___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_Comment___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Xml_Parser_PEReference___closed__3;
static lean_object* l_Lean_Xml_Parser_quote___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_S___lambda__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_SystemLiteral___closed__1___boxed__const__1;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__6;
static lean_object* l_Lean_Xml_Parser_ExternalID___closed__1;
static lean_object* l_Lean_Xml_Parser_doctypedecl___closed__6;
static lean_object* l_Lean_Xml_Parser_EntityRef___closed__4;
static lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__10;
static lean_object* l_Lean_Xml_Parser_NameChar___closed__5;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_contentspec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_doctypedecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_XMLdecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_prolog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NotationType(lean_object*);
static lean_object* l_Lean_Xml_Parser_PITarget___closed__12;
static lean_object* l_Lean_Xml_Parser_NameChar___closed__3;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__19;
static lean_object* l_Lean_Xml_Parser_CharRef___lambda__2___closed__1;
static lean_object* l_Lean_Xml_Parser_quote___rarg___closed__3;
static lean_object* l_Lean_Xml_Parser_seq___lambda__1___closed__2;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
static lean_object* l_Lean_Xml_Parser_cp___closed__4;
static lean_object* l_Lean_Xml_Parser_SystemLiteral___closed__3;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_elementPrefix(lean_object*);
static lean_object* l_Lean_Xml_Parser_cp___closed__8;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityDef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PublicID(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_elementPrefix___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Nmtoken(lean_object*);
static lean_object* l_Lean_Xml_Parser_seq___lambda__1___closed__1;
static lean_object* l_Lean_Xml_Parser_CDEnd___closed__1;
static lean_object* l_Lean_Xml_Parser_ExternalID___closed__2;
static lean_object* l_Lean_Xml_Parser_seq___closed__1;
static lean_object* l_Lean_Xml_Parser_quote___rarg___closed__5;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_PubidChar___closed__1;
static lean_object* l_Lean_Xml_Parser_EntityRef___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NDataDecl(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_Comment___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_Char___closed__2;
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
static lean_object* l_Lean_Xml_Parser_quote___rarg___closed__6;
static lean_object* l_Lean_Xml_Parser_TokenizedType___closed__2;
static lean_object* l_Lean_Xml_Parser_EntityRef___closed__6;
extern lean_object* l_Lean_Xml_instInhabitedContent;
static lean_object* l_Lean_Xml_Parser_TokenizedType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_ETag(lean_object*);
uint32_t l_String_Iterator_curr(lean_object*);
LEAN_EXPORT lean_object* l_Array_back___at_Lean_Xml_Parser_content___spec__1(lean_object*);
static lean_object* l_Lean_Xml_Parser_TokenizedType___closed__6;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__16;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttType(lean_object*);
static lean_object* l_Lean_Xml_Parser_endl___closed__5;
static lean_object* l_Lean_Xml_Parser_NameChar___closed__7;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PEDef(lean_object*);
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__11;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NameChar___boxed__const__2;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__11;
static lean_object* l_Lean_Xml_Parser_Eq___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_AttValue___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_Char___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_content(lean_object*);
static lean_object* l_Lean_Xml_Parser_endl___closed__3;
static lean_object* l_Lean_Xml_Parser_PubidLiteral___closed__3;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PubidChar(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_NameChar___closed__10;
extern lean_object* l_Lean_Parsec_unexpectedEndOfInput;
static lean_object* l_Lean_Xml_Parser_SystemLiteral___closed__4;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__10;
static lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__6;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Enumeration___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttValue___lambda__1(uint32_t, lean_object*);
static lean_object* l_Lean_Xml_Parser_AttlistDecl___closed__1;
lean_object* l_Lean_Parsec_manyCharsCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Reference(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Xml_Parser_NameStartChar___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_VersionNum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_seq___lambda__1(lean_object*);
static lean_object* l_Lean_Xml_Parser_PI___closed__2;
static lean_object* l_Lean_Xml_Parser_CData___closed__1;
static lean_object* l_Lean_Xml_Parser_NotationDecl___closed__1;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__16;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NotationDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Comment___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_TokenizedType(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__5;
static lean_object* l_Lean_Xml_Parser_Char___closed__4;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__20;
static lean_object* l_Lean_Xml_Parser_EncodingDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Enumeration(lean_object*);
static lean_object* l_Lean_Xml_Parser_SystemLiteral___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Char___boxed__const__1;
static lean_object* l_Lean_Xml_Parser_TokenizedType___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Xml_Parser_content___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_SystemLiteral___closed__1;
static lean_object* l_Lean_Xml_Parser_SDDecl___lambda__1___closed__2;
static lean_object* l_Lean_Xml_Parser_EntityValue___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_endl(lean_object*);
static lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__8;
static lean_object* l_Lean_Xml_Parser_Enumeration___closed__1;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__24;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__7;
static lean_object* l_Lean_Xml_Parser_endl___closed__7;
static lean_object* l_Lean_Xml_Parser_PITarget___closed__7;
static lean_object* l_Lean_Xml_Parser_EntityValue___closed__1;
static lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__4;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_STag(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CData___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Xml_Parser_NameStartChar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Xml_Parser_SDDecl___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Eq(lean_object*);
static lean_object* l_Lean_Xml_Parser_Mixed___closed__7;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_hexDigitToNat___boxed(lean_object*);
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__10;
static lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__1;
static uint8_t l_Lean_Xml_Parser_NameStartChar___closed__4;
static lean_object* l_Lean_Xml_Parser_cp___closed__9;
static lean_object* l_Lean_Xml_Parser_Name___closed__1;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__9___boxed__const__1;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__23;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_SystemLiteral___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_element(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_choice(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_children(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__3___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__4(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__13;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Comment(lean_object*);
static lean_object* l_Lean_Xml_Parser_content___closed__1;
LEAN_EXPORT uint8_t l_Lean_Xml_Parser_SystemLiteral___lambda__1(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PI(lean_object*);
static lean_object* l_Lean_Xml_Parser_endl___closed__1;
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
static lean_object* l_Lean_Xml_Parser_NameStartChar___closed__1;
static lean_object* l_Lean_Xml_Parser_endl___closed__2;
static lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__21;
static lean_object* l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
lean_object* lean_uint32_to_nat(uint32_t);
static uint8_t l_Lean_Xml_Parser_NameStartChar___closed__2;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PubidLiteral(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NameChar___boxed__const__3;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___closed__6___boxed__const__1;
static lean_object* l_Lean_Xml_Parser_S___closed__1;
static lean_object* l_Lean_Xml_Parser_TokenizedType___closed__7;
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NameChar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CDSect(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Xml_Parser_CharData___lambda__1(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_S___lambda__1(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Char_ofNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_content___lambda__1(lean_object*);
static lean_object* _init_l_Lean_Xml_Parser_endl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_endl___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 10;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_endl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected: '");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_endl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_endl___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_endl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_endl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__4;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_endl___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\x0d\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_endl___closed__8() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 13;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_endl___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_endl___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_endl___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__9;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_endl___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_endl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Xml_Parser_endl___closed__7;
lean_inc(x_1);
x_19 = l_Lean_Parsec_pstring(x_18, x_1);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 1);
lean_dec(x_21);
x_22 = l_Lean_Xml_Parser_endl___boxed__const__1;
lean_ctor_set(x_19, 1, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Xml_Parser_endl___boxed__const__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
x_29 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_27);
if (x_29 == 0)
{
lean_dec(x_1);
return x_19;
}
else
{
uint32_t x_30; uint8_t x_31; 
lean_dec(x_28);
lean_dec(x_27);
x_30 = 13;
x_31 = l_String_Iterator_hasNext(x_1);
if (x_31 == 0)
{
lean_object* x_32; 
lean_free_object(x_19);
x_32 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_32;
goto block_17;
}
else
{
lean_object* x_33; uint32_t x_34; uint8_t x_35; 
lean_inc(x_1);
x_33 = l_String_Iterator_next(x_1);
x_34 = l_String_Iterator_curr(x_1);
x_35 = x_34 == x_30;
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_free_object(x_19);
x_36 = l_Lean_Xml_Parser_endl___closed__10;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_36;
goto block_17;
}
else
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = l_Lean_Xml_Parser_endl___boxed__const__1;
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 1, x_37);
lean_ctor_set(x_19, 0, x_33);
return x_19;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_1);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
uint32_t x_42; uint8_t x_43; 
lean_dec(x_39);
lean_dec(x_38);
x_42 = 13;
x_43 = l_String_Iterator_hasNext(x_1);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_44;
goto block_17;
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
lean_inc(x_1);
x_45 = l_String_Iterator_next(x_1);
x_46 = l_String_Iterator_curr(x_1);
x_47 = x_46 == x_42;
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_45);
x_48 = l_Lean_Xml_Parser_endl___closed__10;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_48;
goto block_17;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_1);
x_49 = l_Lean_Xml_Parser_endl___boxed__const__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
block_17:
{
uint8_t x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint32_t x_6; uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = 10;
x_7 = l_String_Iterator_hasNext(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parsec_unexpectedEndOfInput;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; uint32_t x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_String_Iterator_next(x_1);
x_11 = l_String_Iterator_curr(x_1);
x_12 = x_11 == x_6;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = l_Lean_Xml_Parser_endl___closed__6;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = l_Lean_Xml_Parser_endl___boxed__const__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_quote___rarg___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 34;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_quote___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_quote___rarg___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_quote___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_quote___rarg___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_quote___rarg___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 39;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_quote___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_quote___rarg___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_quote___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_quote___rarg___closed__5;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_quote___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_43; 
x_3 = 39;
x_43 = l_String_Iterator_hasNext(x_2);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_2);
x_4 = x_2;
x_5 = x_44;
goto block_42;
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
lean_inc(x_2);
x_45 = l_String_Iterator_next(x_2);
x_46 = l_String_Iterator_curr(x_2);
x_47 = x_46 == x_3;
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_45);
x_48 = l_Lean_Xml_Parser_quote___rarg___closed__6;
lean_inc(x_2);
x_4 = x_2;
x_5 = x_48;
goto block_42;
}
else
{
lean_object* x_49; 
lean_inc(x_1);
x_49 = lean_apply_1(x_1, x_45);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
x_53 = l_String_Iterator_hasNext(x_51);
if (x_53 == 0)
{
lean_object* x_54; 
lean_free_object(x_49);
lean_dec(x_52);
x_54 = l_Lean_Parsec_unexpectedEndOfInput;
x_4 = x_51;
x_5 = x_54;
goto block_42;
}
else
{
lean_object* x_55; uint32_t x_56; uint8_t x_57; 
lean_inc(x_51);
x_55 = l_String_Iterator_next(x_51);
x_56 = l_String_Iterator_curr(x_51);
x_57 = x_56 == x_3;
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_55);
lean_free_object(x_49);
lean_dec(x_52);
x_58 = l_Lean_Xml_Parser_quote___rarg___closed__6;
x_4 = x_51;
x_5 = x_58;
goto block_42;
}
else
{
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_49, 0);
x_60 = lean_ctor_get(x_49, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_49);
x_61 = l_String_Iterator_hasNext(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
x_62 = l_Lean_Parsec_unexpectedEndOfInput;
x_4 = x_59;
x_5 = x_62;
goto block_42;
}
else
{
lean_object* x_63; uint32_t x_64; uint8_t x_65; 
lean_inc(x_59);
x_63 = l_String_Iterator_next(x_59);
x_64 = l_String_Iterator_curr(x_59);
x_65 = x_64 == x_3;
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_63);
lean_dec(x_60);
x_66 = l_Lean_Xml_Parser_quote___rarg___closed__6;
x_4 = x_59;
x_5 = x_66;
goto block_42;
}
else
{
lean_object* x_67; 
lean_dec(x_59);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_60);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_49, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
lean_dec(x_49);
x_4 = x_68;
x_5 = x_69;
goto block_42;
}
}
}
block_42:
{
uint8_t x_6; 
x_6 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 34;
x_9 = l_String_Iterator_hasNext(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = l_Lean_Parsec_unexpectedEndOfInput;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
lean_inc(x_2);
x_12 = l_String_Iterator_next(x_2);
x_13 = l_String_Iterator_curr(x_2);
x_14 = x_13 == x_8;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_1);
x_15 = l_Lean_Xml_Parser_quote___rarg___closed__3;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_apply_1(x_1, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_String_Iterator_hasNext(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
x_22 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_22);
return x_17;
}
else
{
lean_object* x_23; uint32_t x_24; uint8_t x_25; 
lean_inc(x_19);
x_23 = l_String_Iterator_next(x_19);
x_24 = l_String_Iterator_curr(x_19);
x_25 = x_24 == x_8;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_20);
x_26 = l_Lean_Xml_Parser_quote___rarg___closed__3;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_26);
return x_17;
}
else
{
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = l_String_Iterator_hasNext(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
x_30 = l_Lean_Parsec_unexpectedEndOfInput;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; uint32_t x_33; uint8_t x_34; 
lean_inc(x_27);
x_32 = l_String_Iterator_next(x_27);
x_33 = l_String_Iterator_curr(x_27);
x_34 = x_33 == x_8;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_28);
x_35 = l_Lean_Xml_Parser_quote___rarg___closed__3;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_28);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_quote(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_quote___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Char___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 9;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Char___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_Char___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Char___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_Char___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Char___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected xml char");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Char___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 9;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Char(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_22; 
x_22 = l_String_Iterator_hasNext(x_1);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_23;
goto block_21;
}
else
{
lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_51; uint8_t x_52; 
lean_inc(x_1);
x_24 = l_String_Iterator_next(x_1);
x_25 = l_String_Iterator_curr(x_1);
x_26 = lean_uint32_to_nat(x_25);
x_51 = lean_unsigned_to_nat(32u);
x_52 = lean_nat_dec_le(x_51, x_26);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_27 = x_53;
goto block_50;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_unsigned_to_nat(55295u);
x_55 = lean_nat_dec_le(x_26, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_27 = x_56;
goto block_50;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_26);
lean_dec(x_1);
x_57 = lean_box_uint32(x_25);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_24);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
block_50:
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_27);
x_28 = lean_unsigned_to_nat(57344u);
x_29 = lean_nat_dec_le(x_28, x_26);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(65536u);
x_31 = lean_nat_dec_le(x_30, x_26);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_24);
x_32 = l_Lean_Xml_Parser_Char___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_32;
goto block_21;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(1114111u);
x_34 = lean_nat_dec_le(x_26, x_33);
lean_dec(x_26);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_24);
x_35 = l_Lean_Xml_Parser_Char___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_35;
goto block_21;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = lean_box_uint32(x_25);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(65533u);
x_39 = lean_nat_dec_le(x_26, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_unsigned_to_nat(65536u);
x_41 = lean_nat_dec_le(x_40, x_26);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_26);
lean_dec(x_24);
x_42 = l_Lean_Xml_Parser_Char___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_42;
goto block_21;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(1114111u);
x_44 = lean_nat_dec_le(x_26, x_43);
lean_dec(x_26);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_24);
x_45 = l_Lean_Xml_Parser_Char___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_45;
goto block_21;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_46 = lean_box_uint32(x_25);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_24);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_26);
lean_dec(x_1);
x_48 = lean_box_uint32(x_25);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_24);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
block_21:
{
uint8_t x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint32_t x_6; uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = 9;
x_7 = l_String_Iterator_hasNext(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Parsec_unexpectedEndOfInput;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Xml_Parser_endl(x_1);
return x_11;
}
}
else
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
lean_inc(x_1);
x_12 = l_String_Iterator_next(x_1);
x_13 = l_String_Iterator_curr(x_1);
x_14 = x_13 == x_6;
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Xml_Parser_Char___closed__3;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Xml_Parser_endl(x_1);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = l_Lean_Xml_Parser_Char___boxed__const__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_S___lambda__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 9;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_S___lambda__1(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_40; 
x_40 = l_String_Iterator_hasNext(x_2);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_2);
x_3 = x_2;
x_4 = x_41;
goto block_39;
}
else
{
lean_object* x_42; uint32_t x_43; uint8_t x_44; 
lean_inc(x_2);
x_42 = l_String_Iterator_next(x_2);
x_43 = l_String_Iterator_curr(x_2);
x_44 = x_43 == x_1;
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_42);
x_45 = l_Lean_Xml_Parser_endl___closed__1;
x_46 = lean_string_push(x_45, x_1);
x_47 = l_Lean_Xml_Parser_endl___closed__3;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_Xml_Parser_endl___closed__5;
x_50 = lean_string_append(x_48, x_49);
lean_inc(x_2);
x_3 = x_2;
x_4 = x_50;
goto block_39;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
x_51 = lean_box_uint32(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
block_39:
{
uint8_t x_5; 
x_5 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
x_7 = l_Lean_Xml_Parser_endl(x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_13);
if (x_15 == 0)
{
lean_dec(x_2);
return x_7;
}
else
{
uint32_t x_16; uint8_t x_17; 
lean_dec(x_14);
lean_dec(x_13);
x_16 = 9;
x_17 = l_String_Iterator_hasNext(x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set(x_7, 1, x_18);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
else
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
lean_inc(x_2);
x_19 = l_String_Iterator_next(x_2);
x_20 = l_String_Iterator_curr(x_2);
x_21 = x_20 == x_16;
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = l_Lean_Xml_Parser_Char___closed__3;
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
else
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = l_Lean_Xml_Parser_S___lambda__1___boxed__const__1;
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_23);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
else
{
uint32_t x_28; uint8_t x_29; 
lean_dec(x_25);
lean_dec(x_24);
x_28 = 9;
x_29 = l_String_Iterator_hasNext(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Parsec_unexpectedEndOfInput;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; uint32_t x_33; uint8_t x_34; 
lean_inc(x_2);
x_32 = l_String_Iterator_next(x_2);
x_33 = l_String_Iterator_curr(x_2);
x_34 = x_33 == x_28;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
x_35 = l_Lean_Xml_Parser_Char___closed__3;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_37 = l_Lean_Xml_Parser_S___lambda__1___boxed__const__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_S___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 32;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_S___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_S___closed__1___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_S___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_S(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_S___closed__1;
x_3 = l_Lean_Parsec_many1Chars(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_S___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Xml_Parser_S___lambda__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Eq___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 61;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Eq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_Eq___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Eq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_Eq___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Eq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_31; 
lean_inc(x_1);
x_31 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_2 = x_32;
goto block_30;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
x_36 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_34);
if (x_36 == 0)
{
lean_dec(x_1);
return x_31;
}
else
{
lean_free_object(x_31);
lean_dec(x_35);
lean_dec(x_34);
x_2 = x_1;
goto block_30;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_1);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_dec(x_38);
lean_dec(x_37);
x_2 = x_1;
goto block_30;
}
}
}
block_30:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 61;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_Eq___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_inc(x_7);
x_12 = l_Lean_Xml_Parser_S(x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 1, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
x_22 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_7, x_20);
if (x_22 == 0)
{
lean_dec(x_7);
return x_12;
}
else
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_20);
x_23 = lean_box(0);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 1, x_23);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_7, x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(192u);
x_2 = lean_unsigned_to_nat(214u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(216u);
x_2 = lean_unsigned_to_nat(246u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(248u);
x_2 = lean_unsigned_to_nat(767u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(880u);
x_2 = lean_unsigned_to_nat(893u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(895u);
x_2 = lean_unsigned_to_nat(8191u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8204u);
x_2 = lean_unsigned_to_nat(8205u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8304u);
x_2 = lean_unsigned_to_nat(8591u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(11264u);
x_2 = lean_unsigned_to_nat(12271u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(12289u);
x_2 = lean_unsigned_to_nat(55295u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(63744u);
x_2 = lean_unsigned_to_nat(64975u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(65008u);
x_2 = lean_unsigned_to_nat(65533u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(65536u);
x_2 = lean_unsigned_to_nat(983039u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__13;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__14;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__15;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__16;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__17;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__18;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__19;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__20;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__21;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__9;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__22;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__23;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__24;
x_2 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__25;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Xml_Parser_NameStartChar___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_7, x_1);
lean_dec(x_7);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
lean_dec(x_8);
x_10 = 1;
x_11 = x_3 + x_10;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_1, x_8);
lean_dec(x_8);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = x_3 + x_14;
x_3 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameStartChar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Xml_Parser_NameStartChar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Xml_Parser_NameStartChar___closed__1;
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameStartChar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected a name character");
return x_1;
}
}
static uint8_t _init_l_Lean_Xml_Parser_NameStartChar___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Xml_Parser_NameStartChar___closed__1;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Xml_Parser_NameStartChar___closed__5() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Xml_Parser_NameStartChar___closed__1;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NameStartChar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parsec_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; uint32_t x_32; uint8_t x_33; 
lean_inc(x_1);
x_5 = l_String_Iterator_next(x_1);
x_6 = l_String_Iterator_curr(x_1);
x_32 = 65;
x_33 = x_32 <= x_6;
if (x_33 == 0)
{
uint32_t x_34; uint8_t x_35; 
x_34 = 97;
x_35 = x_34 <= x_6;
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
x_7 = x_36;
goto block_31;
}
else
{
uint32_t x_37; uint8_t x_38; 
x_37 = 122;
x_38 = x_6 <= x_37;
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
x_7 = x_39;
goto block_31;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_40 = lean_box_uint32(x_6);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint32_t x_42; uint8_t x_43; 
x_42 = 90;
x_43 = x_6 <= x_42;
if (x_43 == 0)
{
uint32_t x_44; uint8_t x_45; 
x_44 = 97;
x_45 = x_44 <= x_6;
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
x_7 = x_46;
goto block_31;
}
else
{
uint32_t x_47; uint8_t x_48; 
x_47 = 122;
x_48 = x_6 <= x_47;
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_box(0);
x_7 = x_49;
goto block_31;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_50 = lean_box_uint32(x_6);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_5);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_52 = lean_box_uint32(x_6);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_5);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
block_31:
{
uint32_t x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = 58;
x_9 = x_6 == x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 95;
x_11 = x_6 == x_10;
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Xml_Parser_NameStartChar___closed__2;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = l_Lean_Xml_Parser_NameStartChar___closed__3;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = l_Lean_Xml_Parser_NameStartChar___closed__4;
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = l_Lean_Xml_Parser_NameStartChar___closed__3;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; size_t x_19; lean_object* x_20; size_t x_21; uint8_t x_22; 
x_18 = lean_uint32_to_nat(x_6);
x_19 = 0;
x_20 = l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges;
x_21 = l_Lean_Xml_Parser_NameStartChar___closed__5;
x_22 = l_Array_anyMUnsafe_any___at_Lean_Xml_Parser_NameStartChar___spec__1(x_18, x_20, x_19, x_21);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_23 = l_Lean_Xml_Parser_NameStartChar___closed__3;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_box_uint32(x_6);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_box_uint32(x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = lean_box_uint32(x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Xml_Parser_NameStartChar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Xml_Parser_NameStartChar___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("condition not satisfied");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 183;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_NameChar___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_NameChar___closed__3;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__5() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 46;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_NameChar___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_NameChar___closed__6;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__8() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 45;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_NameChar___closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_NameChar___closed__9;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("digit expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 183;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 46;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NameChar___boxed__const__3() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 45;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NameChar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_NameStartChar(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_9 = x_2;
} else {
 lean_dec_ref(x_2);
 x_9 = lean_box(0);
}
x_10 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
if (lean_is_scalar(x_9)) {
 x_11 = lean_alloc_ctor(1, 2, 0);
} else {
 x_11 = x_9;
}
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_90; 
lean_dec(x_8);
lean_dec(x_7);
x_90 = l_String_Iterator_hasNext(x_1);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_12 = x_1;
x_13 = x_91;
goto block_89;
}
else
{
lean_object* x_92; uint32_t x_93; uint32_t x_94; uint8_t x_95; 
lean_inc(x_1);
x_92 = l_String_Iterator_next(x_1);
x_93 = l_String_Iterator_curr(x_1);
x_94 = 48;
x_95 = x_94 <= x_93;
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_92);
x_96 = l_Lean_Xml_Parser_NameChar___closed__11;
lean_inc(x_1);
x_12 = x_1;
x_13 = x_96;
goto block_89;
}
else
{
uint32_t x_97; uint8_t x_98; 
x_97 = 57;
x_98 = x_93 <= x_97;
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_92);
x_99 = l_Lean_Xml_Parser_NameChar___closed__11;
lean_inc(x_1);
x_12 = x_1;
x_13 = x_99;
goto block_89;
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_9);
lean_dec(x_1);
x_100 = lean_box_uint32(x_93);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_89:
{
uint8_t x_14; 
x_14 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
if (lean_is_scalar(x_9)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_9;
}
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
uint32_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_81; 
lean_dec(x_13);
lean_dec(x_12);
x_16 = 45;
x_81 = l_String_Iterator_hasNext(x_1);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_17 = x_1;
x_18 = x_82;
goto block_80;
}
else
{
lean_object* x_83; uint32_t x_84; uint8_t x_85; 
lean_inc(x_1);
x_83 = l_String_Iterator_next(x_1);
x_84 = l_String_Iterator_curr(x_1);
x_85 = x_84 == x_16;
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_83);
x_86 = l_Lean_Xml_Parser_NameChar___closed__10;
lean_inc(x_1);
x_17 = x_1;
x_18 = x_86;
goto block_80;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_9);
lean_dec(x_1);
x_87 = l_Lean_Xml_Parser_NameChar___boxed__const__3;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
block_80:
{
uint8_t x_19; 
x_19 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_1);
if (lean_is_scalar(x_9)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_9;
}
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
uint32_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_72; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = 46;
x_72 = l_String_Iterator_hasNext(x_1);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_22 = x_1;
x_23 = x_73;
goto block_71;
}
else
{
lean_object* x_74; uint32_t x_75; uint8_t x_76; 
lean_inc(x_1);
x_74 = l_String_Iterator_next(x_1);
x_75 = l_String_Iterator_curr(x_1);
x_76 = x_75 == x_21;
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_74);
x_77 = l_Lean_Xml_Parser_NameChar___closed__7;
lean_inc(x_1);
x_22 = x_1;
x_23 = x_77;
goto block_71;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_9);
lean_dec(x_1);
x_78 = l_Lean_Xml_Parser_NameChar___boxed__const__2;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
block_71:
{
uint8_t x_24; 
x_24 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
if (lean_is_scalar(x_9)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_9;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
else
{
uint32_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_63; 
lean_dec(x_23);
lean_dec(x_22);
x_26 = 183;
x_63 = l_String_Iterator_hasNext(x_1);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_27 = x_1;
x_28 = x_64;
goto block_62;
}
else
{
lean_object* x_65; uint32_t x_66; uint8_t x_67; 
lean_inc(x_1);
x_65 = l_String_Iterator_next(x_1);
x_66 = l_String_Iterator_curr(x_1);
x_67 = x_66 == x_26;
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_65);
x_68 = l_Lean_Xml_Parser_NameChar___closed__4;
lean_inc(x_1);
x_27 = x_1;
x_28 = x_68;
goto block_62;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_9);
lean_dec(x_1);
x_69 = l_Lean_Xml_Parser_NameChar___boxed__const__1;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
block_62:
{
uint8_t x_29; 
x_29 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_1);
if (lean_is_scalar(x_9)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_9;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_28);
lean_dec(x_27);
x_31 = l_String_Iterator_hasNext(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_9)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_9;
}
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; uint32_t x_35; uint32_t x_36; uint8_t x_37; 
lean_inc(x_1);
x_34 = l_String_Iterator_next(x_1);
x_35 = l_String_Iterator_curr(x_1);
x_36 = 768;
x_37 = x_36 <= x_35;
if (x_37 == 0)
{
uint32_t x_38; uint8_t x_39; 
x_38 = 8255;
x_39 = x_38 <= x_35;
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_34);
x_40 = l_Lean_Xml_Parser_NameChar___closed__1;
if (lean_is_scalar(x_9)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_9;
}
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
uint32_t x_42; uint8_t x_43; 
x_42 = 8256;
x_43 = x_35 <= x_42;
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
x_44 = l_Lean_Xml_Parser_NameChar___closed__1;
if (lean_is_scalar(x_9)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_9;
}
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_46 = lean_box_uint32(x_35);
if (lean_is_scalar(x_9)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_9;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint32_t x_48; uint8_t x_49; 
x_48 = 879;
x_49 = x_35 <= x_48;
if (x_49 == 0)
{
uint32_t x_50; uint8_t x_51; 
x_50 = 8255;
x_51 = x_50 <= x_35;
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_34);
x_52 = l_Lean_Xml_Parser_NameChar___closed__1;
if (lean_is_scalar(x_9)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_9;
}
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
else
{
uint32_t x_54; uint8_t x_55; 
x_54 = 8256;
x_55 = x_35 <= x_54;
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_34);
x_56 = l_Lean_Xml_Parser_NameChar___closed__1;
if (lean_is_scalar(x_9)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_9;
}
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_58 = lean_box_uint32(x_35);
if (lean_is_scalar(x_9)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_9;
 lean_ctor_set_tag(x_59, 0);
}
lean_ctor_set(x_59, 0, x_34);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_1);
x_60 = lean_box_uint32(x_35);
if (lean_is_scalar(x_9)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_9;
 lean_ctor_set_tag(x_61, 0);
}
lean_ctor_set(x_61, 0, x_34);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_Name___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_NameChar), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Name(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_NameStartChar(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Xml_Parser_endl___closed__1;
x_6 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_7 = lean_string_push(x_5, x_6);
x_8 = l_Lean_Xml_Parser_Name___closed__1;
x_9 = l_Lean_Parsec_manyCharsCore(x_8, x_7, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_VersionNum___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("1.");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_VersionNum___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parsec_digit), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_VersionNum(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_VersionNum___closed__1;
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Xml_Parser_VersionNum___closed__2;
x_6 = l_Lean_Parsec_many1(lean_box(0));
x_7 = lean_apply_2(x_6, x_5, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_7, 1, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_VersionInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("version");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_VersionInfo___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_VersionNum), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_VersionInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Xml_Parser_VersionInfo___closed__1;
x_5 = l_Lean_Parsec_pstring(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Xml_Parser_Eq(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Xml_Parser_VersionInfo___closed__2;
x_10 = l_Lean_Xml_Parser_quote___rarg(x_9, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_EncName___lambda__1___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 95;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EncName___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_EncName___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EncName___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_EncName___lambda__1___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EncName___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ASCII letter expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 46;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 95;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__3() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 45;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EncName___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_63; 
x_63 = l_String_Iterator_hasNext(x_1);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_64;
goto block_62;
}
else
{
lean_object* x_65; uint32_t x_66; uint32_t x_67; uint8_t x_68; 
lean_inc(x_1);
x_65 = l_String_Iterator_next(x_1);
x_66 = l_String_Iterator_curr(x_1);
x_67 = 65;
x_68 = x_67 <= x_66;
if (x_68 == 0)
{
uint32_t x_69; uint8_t x_70; 
x_69 = 97;
x_70 = x_69 <= x_66;
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_65);
x_71 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_71;
goto block_62;
}
else
{
uint32_t x_72; uint8_t x_73; 
x_72 = 122;
x_73 = x_66 <= x_72;
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_65);
x_74 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_74;
goto block_62;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_1);
x_75 = lean_box_uint32(x_66);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint32_t x_77; uint8_t x_78; 
x_77 = 90;
x_78 = x_66 <= x_77;
if (x_78 == 0)
{
uint32_t x_79; uint8_t x_80; 
x_79 = 97;
x_80 = x_79 <= x_66;
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_65);
x_81 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_81;
goto block_62;
}
else
{
uint32_t x_82; uint8_t x_83; 
x_82 = 122;
x_83 = x_66 <= x_82;
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_65);
x_84 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_84;
goto block_62;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_1);
x_85 = lean_box_uint32(x_66);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_65);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_87 = lean_box_uint32(x_66);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_65);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
block_62:
{
uint8_t x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_50; 
lean_dec(x_3);
lean_dec(x_2);
x_50 = l_String_Iterator_hasNext(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_6 = x_1;
x_7 = x_51;
goto block_49;
}
else
{
lean_object* x_52; uint32_t x_53; uint32_t x_54; uint8_t x_55; 
lean_inc(x_1);
x_52 = l_String_Iterator_next(x_1);
x_53 = l_String_Iterator_curr(x_1);
x_54 = 48;
x_55 = x_54 <= x_53;
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
x_56 = l_Lean_Xml_Parser_NameChar___closed__11;
lean_inc(x_1);
x_6 = x_1;
x_7 = x_56;
goto block_49;
}
else
{
uint32_t x_57; uint8_t x_58; 
x_57 = 57;
x_58 = x_53 <= x_57;
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_52);
x_59 = l_Lean_Xml_Parser_NameChar___closed__11;
lean_inc(x_1);
x_6 = x_1;
x_7 = x_59;
goto block_49;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_1);
x_60 = lean_box_uint32(x_53);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
block_49:
{
uint8_t x_8; 
x_8 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 45;
x_41 = l_String_Iterator_hasNext(x_1);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_11 = x_1;
x_12 = x_42;
goto block_40;
}
else
{
lean_object* x_43; uint32_t x_44; uint8_t x_45; 
lean_inc(x_1);
x_43 = l_String_Iterator_next(x_1);
x_44 = l_String_Iterator_curr(x_1);
x_45 = x_44 == x_10;
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_43);
x_46 = l_Lean_Xml_Parser_NameChar___closed__10;
lean_inc(x_1);
x_11 = x_1;
x_12 = x_46;
goto block_40;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_47 = l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__3;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
block_40:
{
uint8_t x_13; 
x_13 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
uint32_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
x_15 = 95;
x_32 = l_String_Iterator_hasNext(x_1);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_16 = x_1;
x_17 = x_33;
goto block_31;
}
else
{
lean_object* x_34; uint32_t x_35; uint8_t x_36; 
lean_inc(x_1);
x_34 = l_String_Iterator_next(x_1);
x_35 = l_String_Iterator_curr(x_1);
x_36 = x_35 == x_15;
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_34);
x_37 = l_Lean_Xml_Parser_EncName___lambda__1___closed__3;
lean_inc(x_1);
x_16 = x_1;
x_17 = x_37;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_38 = l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__2;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
block_31:
{
uint8_t x_18; 
x_18 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
uint32_t x_20; uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_16);
x_20 = 46;
x_21 = l_String_Iterator_hasNext(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Parsec_unexpectedEndOfInput;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
lean_inc(x_1);
x_24 = l_String_Iterator_next(x_1);
x_25 = l_String_Iterator_curr(x_1);
x_26 = x_25 == x_20;
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
x_27 = l_Lean_Xml_Parser_NameChar___closed__7;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__1;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_EncName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_EncName___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EncName(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parsec_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
lean_inc(x_1);
x_5 = l_String_Iterator_next(x_1);
x_6 = l_String_Iterator_curr(x_1);
x_7 = 65;
x_8 = x_7 <= x_6;
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 97;
x_10 = x_9 <= x_6;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 122;
x_14 = x_6 <= x_13;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_17 = l_Lean_Xml_Parser_endl___closed__1;
x_18 = lean_string_push(x_17, x_6);
x_19 = l_Lean_Xml_Parser_EncName___closed__1;
x_20 = l_Lean_Parsec_manyCharsCore(x_19, x_18, x_5);
return x_20;
}
}
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 90;
x_22 = x_6 <= x_21;
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 97;
x_24 = x_23 <= x_6;
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_25 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = 122;
x_28 = x_6 <= x_27;
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
x_29 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_31 = l_Lean_Xml_Parser_endl___closed__1;
x_32 = lean_string_push(x_31, x_6);
x_33 = l_Lean_Xml_Parser_EncName___closed__1;
x_34 = l_Lean_Parsec_manyCharsCore(x_33, x_32, x_5);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_35 = l_Lean_Xml_Parser_endl___closed__1;
x_36 = lean_string_push(x_35, x_6);
x_37 = l_Lean_Xml_Parser_EncName___closed__1;
x_38 = l_Lean_Parsec_manyCharsCore(x_37, x_36, x_5);
return x_38;
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_EncodingDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("encoding");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EncodingDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_EncName), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EncodingDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Xml_Parser_EncodingDecl___closed__1;
x_5 = l_Lean_Parsec_pstring(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Xml_Parser_Eq(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Xml_Parser_EncodingDecl___closed__2;
x_10 = l_Lean_Xml_Parser_quote___rarg(x_9, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_SDDecl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("yes");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_SDDecl___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_SDDecl___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_SDDecl___lambda__1___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
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
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_9);
if (x_11 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_3);
lean_dec(x_10);
lean_dec(x_9);
x_12 = l_Lean_Xml_Parser_SDDecl___lambda__1___closed__2;
x_13 = l_Lean_Parsec_pstring(x_12, x_1);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = l_Lean_Xml_Parser_SDDecl___lambda__1___closed__2;
x_19 = l_Lean_Parsec_pstring(x_18, x_1);
return x_19;
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_SDDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("standalone");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_SDDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_SDDecl___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_SDDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Xml_Parser_SDDecl___closed__1;
x_5 = l_Lean_Parsec_pstring(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Xml_Parser_Eq(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Xml_Parser_SDDecl___closed__2;
x_10 = l_Lean_Xml_Parser_quote___rarg(x_9, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_XMLdecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("?>");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_XMLdecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<?xml");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_XMLdecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_Xml_Parser_XMLdecl___closed__2;
x_49 = l_Lean_Parsec_pstring(x_48, x_1);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Xml_Parser_VersionInfo(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_52);
x_53 = l_Lean_Xml_Parser_EncodingDecl(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_54);
x_55 = l_Lean_Xml_Parser_SDDecl(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_2 = x_56;
goto block_47;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 1);
x_60 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_54, x_58);
if (x_60 == 0)
{
lean_dec(x_54);
return x_55;
}
else
{
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
x_2 = x_54;
goto block_47;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_54, x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_54);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_dec(x_62);
lean_dec(x_61);
x_2 = x_54;
goto block_47;
}
}
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_53);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_53, 0);
x_67 = lean_ctor_get(x_53, 1);
x_68 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_52, x_66);
if (x_68 == 0)
{
lean_dec(x_52);
return x_53;
}
else
{
lean_object* x_69; 
lean_free_object(x_53);
lean_dec(x_67);
lean_dec(x_66);
lean_inc(x_52);
x_69 = l_Lean_Xml_Parser_SDDecl(x_52);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
lean_dec(x_52);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_2 = x_70;
goto block_47;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_ctor_get(x_69, 1);
x_74 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_52, x_72);
if (x_74 == 0)
{
lean_dec(x_52);
return x_69;
}
else
{
lean_free_object(x_69);
lean_dec(x_73);
lean_dec(x_72);
x_2 = x_52;
goto block_47;
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_69, 0);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_69);
x_77 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_52, x_75);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_52);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_dec(x_76);
lean_dec(x_75);
x_2 = x_52;
goto block_47;
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_53, 0);
x_80 = lean_ctor_get(x_53, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_53);
x_81 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_52, x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_52);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
else
{
lean_object* x_83; 
lean_dec(x_80);
lean_dec(x_79);
lean_inc(x_52);
x_83 = l_Lean_Xml_Parser_SDDecl(x_52);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
lean_dec(x_52);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_2 = x_84;
goto block_47;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_87 = x_83;
} else {
 lean_dec_ref(x_83);
 x_87 = lean_box(0);
}
x_88 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_52, x_85);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_52);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
x_2 = x_52;
goto block_47;
}
}
}
}
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_51);
if (x_90 == 0)
{
return x_51;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_51, 0);
x_92 = lean_ctor_get(x_51, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_51);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_49);
if (x_94 == 0)
{
return x_49;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_49, 0);
x_96 = lean_ctor_get(x_49, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_49);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
block_47:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l_Lean_Xml_Parser_S(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Xml_Parser_XMLdecl___closed__1;
x_6 = l_Lean_Parsec_pstring(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_6, 1, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
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
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_18);
if (x_20 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_3);
lean_dec(x_19);
lean_dec(x_18);
x_21 = l_Lean_Xml_Parser_XMLdecl___closed__1;
x_22 = l_Lean_Parsec_pstring(x_21, x_2);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 1, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
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
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
x_35 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_2);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
x_37 = l_Lean_Xml_Parser_XMLdecl___closed__1;
x_38 = l_Lean_Parsec_pstring(x_37, x_2);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_45 = x_38;
} else {
 lean_dec_ref(x_38);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_Comment___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_string_append(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Comment___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_30; 
x_30 = l_String_Iterator_hasNext(x_1);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_31;
goto block_29;
}
else
{
lean_object* x_32; uint32_t x_33; uint32_t x_34; uint8_t x_35; uint8_t x_36; 
lean_inc(x_1);
x_32 = l_String_Iterator_next(x_1);
x_33 = l_String_Iterator_curr(x_1);
x_34 = 45;
x_35 = x_33 == x_34;
x_36 = l_instDecidableNot___rarg(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_32);
x_37 = l_Lean_Xml_Parser_NameChar___closed__1;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_37;
goto block_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_38 = l_Lean_Xml_Parser_endl___closed__1;
x_39 = lean_string_push(x_38, x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
block_29:
{
uint8_t x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint32_t x_6; uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = 45;
x_7 = l_String_Iterator_hasNext(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parsec_unexpectedEndOfInput;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; uint32_t x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_String_Iterator_next(x_1);
x_11 = l_String_Iterator_curr(x_1);
x_12 = x_11 == x_6;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = l_Lean_Xml_Parser_NameChar___closed__10;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = l_String_Iterator_hasNext(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Parsec_unexpectedEndOfInput;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; uint8_t x_21; 
lean_inc(x_10);
x_18 = l_String_Iterator_next(x_10);
x_19 = l_String_Iterator_curr(x_10);
x_20 = x_19 == x_6;
x_21 = l_instDecidableNot___rarg(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
x_22 = l_Lean_Xml_Parser_NameChar___closed__1;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
x_24 = l_Lean_Xml_Parser_endl___closed__1;
x_25 = lean_string_push(x_24, x_19);
x_26 = l_Lean_Xml_Parser_NameChar___closed__8;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_Comment___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<!--");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Comment___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_Comment___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Comment___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-->");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Comment(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_Comment___closed__1;
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Xml_Parser_Comment___closed__2;
x_6 = l_Lean_Parsec_many(lean_box(0));
x_7 = lean_apply_2(x_6, x_5, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
x_13 = l_Lean_Xml_Parser_Comment___closed__3;
x_14 = l_Lean_Parsec_pstring(x_13, x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_dec(x_16);
x_17 = l_Lean_Xml_Parser_endl___closed__1;
lean_ctor_set(x_14, 1, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_Xml_Parser_endl___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
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
x_25 = lean_nat_dec_le(x_10, x_10);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_9);
x_26 = l_Lean_Xml_Parser_Comment___closed__3;
x_27 = l_Lean_Parsec_pstring(x_26, x_8);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_dec(x_29);
x_30 = l_Lean_Xml_Parser_endl___closed__1;
lean_ctor_set(x_27, 1, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_Xml_Parser_endl___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_40 = l_Lean_Xml_Parser_endl___closed__1;
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_Comment___spec__1(x_9, x_38, x_39, x_40);
lean_dec(x_9);
x_42 = l_Lean_Xml_Parser_Comment___closed__3;
x_43 = l_Lean_Parsec_pstring(x_42, x_8);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 1);
lean_dec(x_45);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_41);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_7);
if (x_52 == 0)
{
return x_7;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_7, 0);
x_54 = lean_ctor_get(x_7, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_7);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
return x_3;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_3);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_Comment___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_Comment___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 108;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_PITarget___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_PITarget___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 76;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_PITarget___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_PITarget___closed__5;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__7() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 109;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_PITarget___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_PITarget___closed__8;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__10() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 77;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_PITarget___closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_PITarget___closed__11;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__13() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 120;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_PITarget___closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_PITarget___closed__14;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__16() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 88;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_PITarget___closed__16;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PITarget___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_PITarget___closed__17;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PITarget(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_28; lean_object* x_29; lean_object* x_52; 
x_52 = l_Lean_Xml_Parser_Name(x_1);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint32_t x_70; uint8_t x_71; 
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
x_70 = 88;
x_71 = l_String_Iterator_hasNext(x_53);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_53);
x_56 = x_53;
x_57 = x_72;
goto block_69;
}
else
{
lean_object* x_73; uint32_t x_74; uint8_t x_75; 
lean_inc(x_53);
x_73 = l_String_Iterator_next(x_53);
x_74 = l_String_Iterator_curr(x_53);
x_75 = x_74 == x_70;
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_73);
x_76 = l_Lean_Xml_Parser_PITarget___closed__18;
lean_inc(x_53);
x_56 = x_53;
x_57 = x_76;
goto block_69;
}
else
{
lean_dec(x_55);
lean_dec(x_53);
x_28 = x_73;
x_29 = x_54;
goto block_51;
}
}
block_69:
{
uint8_t x_58; 
x_58 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_53, x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_54);
lean_dec(x_53);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_55;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
uint32_t x_60; uint8_t x_61; 
lean_dec(x_57);
lean_dec(x_56);
x_60 = 120;
x_61 = l_String_Iterator_hasNext(x_53);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_54);
x_62 = l_Lean_Parsec_unexpectedEndOfInput;
if (lean_is_scalar(x_55)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_55;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_53);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
else
{
lean_object* x_64; uint32_t x_65; uint8_t x_66; 
lean_inc(x_53);
x_64 = l_String_Iterator_next(x_53);
x_65 = l_String_Iterator_curr(x_53);
x_66 = x_65 == x_60;
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_64);
lean_dec(x_54);
x_67 = l_Lean_Xml_Parser_PITarget___closed__15;
if (lean_is_scalar(x_55)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_55;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_53);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
lean_dec(x_55);
lean_dec(x_53);
x_28 = x_64;
x_29 = x_54;
goto block_51;
}
}
}
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_52);
if (x_77 == 0)
{
return x_52;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_52, 0);
x_79 = lean_ctor_get(x_52, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_52);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
block_27:
{
lean_object* x_4; lean_object* x_5; uint32_t x_19; uint8_t x_20; 
x_19 = 76;
x_20 = l_String_Iterator_hasNext(x_2);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_2);
x_4 = x_2;
x_5 = x_21;
goto block_18;
}
else
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; 
lean_inc(x_2);
x_22 = l_String_Iterator_next(x_2);
x_23 = l_String_Iterator_curr(x_2);
x_24 = x_23 == x_19;
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = l_Lean_Xml_Parser_PITarget___closed__6;
lean_inc(x_2);
x_4 = x_2;
x_5 = x_25;
goto block_18;
}
else
{
lean_object* x_26; 
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
}
block_18:
{
uint8_t x_6; 
x_6 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 108;
x_9 = l_String_Iterator_hasNext(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = l_Lean_Parsec_unexpectedEndOfInput;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; 
lean_inc(x_2);
x_12 = l_String_Iterator_next(x_2);
x_13 = l_String_Iterator_curr(x_2);
x_14 = x_13 == x_8;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_3);
x_15 = l_Lean_Xml_Parser_PITarget___closed__3;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
}
}
block_51:
{
lean_object* x_30; lean_object* x_31; uint32_t x_44; uint8_t x_45; 
x_44 = 77;
x_45 = l_String_Iterator_hasNext(x_28);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_28);
x_30 = x_28;
x_31 = x_46;
goto block_43;
}
else
{
lean_object* x_47; uint32_t x_48; uint8_t x_49; 
lean_inc(x_28);
x_47 = l_String_Iterator_next(x_28);
x_48 = l_String_Iterator_curr(x_28);
x_49 = x_48 == x_44;
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_47);
x_50 = l_Lean_Xml_Parser_PITarget___closed__12;
lean_inc(x_28);
x_30 = x_28;
x_31 = x_50;
goto block_43;
}
else
{
lean_dec(x_28);
x_2 = x_47;
x_3 = x_29;
goto block_27;
}
}
block_43:
{
uint8_t x_32; 
x_32 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_28, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
uint32_t x_34; uint8_t x_35; 
lean_dec(x_31);
lean_dec(x_30);
x_34 = 109;
x_35 = l_String_Iterator_hasNext(x_28);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_29);
x_36 = l_Lean_Parsec_unexpectedEndOfInput;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
lean_object* x_38; uint32_t x_39; uint8_t x_40; 
lean_inc(x_28);
x_38 = l_String_Iterator_next(x_28);
x_39 = l_String_Iterator_curr(x_28);
x_40 = x_39 == x_34;
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_38);
lean_dec(x_29);
x_41 = l_Lean_Xml_Parser_PITarget___closed__9;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_dec(x_28);
x_2 = x_38;
x_3 = x_29;
goto block_27;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PI___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_XMLdecl___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_Xml_Parser_endl___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = l_Lean_Xml_Parser_endl___closed__1;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = l_Lean_Xml_Parser_Char(x_1);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_PI___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<?");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PI___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_PI___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PI(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_PI___closed__1;
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Xml_Parser_PITarget(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_6);
x_7 = l_Lean_Xml_Parser_S(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Xml_Parser_PI___closed__2;
x_10 = l_Lean_Parsec_manyChars(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Xml_Parser_XMLdecl___closed__1;
x_13 = l_Lean_Parsec_pstring(x_12, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 1, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
x_27 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_6, x_25);
if (x_27 == 0)
{
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_10);
lean_dec(x_26);
lean_dec(x_25);
x_28 = l_Lean_Xml_Parser_XMLdecl___closed__1;
x_29 = l_Lean_Parsec_pstring(x_28, x_6);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 1);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 1, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_6, x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_6);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_40);
x_44 = l_Lean_Xml_Parser_XMLdecl___closed__1;
x_45 = l_Lean_Parsec_pstring(x_44, x_6);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
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
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_52 = x_45;
} else {
 lean_dec_ref(x_45);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_7);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_7, 0);
x_56 = lean_ctor_get(x_7, 1);
x_57 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_6, x_55);
if (x_57 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_free_object(x_7);
lean_dec(x_56);
lean_dec(x_55);
x_58 = l_Lean_Xml_Parser_XMLdecl___closed__1;
x_59 = l_Lean_Parsec_pstring(x_58, x_6);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 1);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set(x_59, 1, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
return x_59;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_59, 0);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_59);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_7, 0);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_7);
x_72 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_6, x_70);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_6);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_71);
lean_dec(x_70);
x_74 = l_Lean_Xml_Parser_XMLdecl___closed__1;
x_75 = l_Lean_Parsec_pstring(x_74, x_6);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_5);
if (x_84 == 0)
{
return x_5;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_5, 0);
x_86 = lean_ctor_get(x_5, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_5);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_3);
if (x_88 == 0)
{
return x_3;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_3, 0);
x_90 = lean_ctor_get(x_3, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_3);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Misc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
x_5 = lean_box(0);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_10);
if (x_12 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_10);
lean_inc(x_1);
x_13 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_1);
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
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
x_21 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_19);
if (x_21 == 0)
{
lean_dec(x_1);
return x_13;
}
else
{
lean_object* x_22; 
lean_free_object(x_13);
lean_dec(x_20);
lean_dec(x_19);
x_22 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 1, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
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
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_33);
x_37 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
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
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_44 = x_37;
} else {
 lean_dec_ref(x_37);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_48 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_1);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_47);
lean_dec(x_46);
lean_inc(x_1);
x_50 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
 x_57 = lean_box(0);
}
x_58 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_55);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_1);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
x_60 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Xml_Parser_SystemLiteral___lambda__1(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = x_2 == x_1;
x_4 = l_instDecidableNot___rarg(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Xml_Parser_SystemLiteral___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 39;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_SystemLiteral___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_SystemLiteral___closed__1___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_SystemLiteral___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_SystemLiteral___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_SystemLiteral___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_satisfy), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_SystemLiteral___closed__3___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_SystemLiteral___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_SystemLiteral___closed__3___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_SystemLiteral___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_SystemLiteral___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_SystemLiteral___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_satisfy), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_SystemLiteral(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_27; 
x_2 = 34;
x_27 = l_String_Iterator_hasNext(x_1);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_3 = x_1;
x_4 = x_28;
goto block_26;
}
else
{
lean_object* x_29; uint32_t x_30; uint8_t x_31; 
lean_inc(x_1);
x_29 = l_String_Iterator_next(x_1);
x_30 = l_String_Iterator_curr(x_1);
x_31 = x_30 == x_2;
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_29);
x_32 = l_Lean_Xml_Parser_quote___rarg___closed__3;
lean_inc(x_1);
x_3 = x_1;
x_4 = x_32;
goto block_26;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Xml_Parser_SystemLiteral___closed__4;
x_34 = l_Lean_Parsec_manyChars(x_33, x_29);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = l_String_Iterator_hasNext(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_free_object(x_34);
lean_dec(x_37);
x_39 = l_Lean_Parsec_unexpectedEndOfInput;
x_3 = x_36;
x_4 = x_39;
goto block_26;
}
else
{
lean_object* x_40; uint32_t x_41; uint8_t x_42; 
lean_inc(x_36);
x_40 = l_String_Iterator_next(x_36);
x_41 = l_String_Iterator_curr(x_36);
x_42 = x_41 == x_2;
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_40);
lean_free_object(x_34);
lean_dec(x_37);
x_43 = l_Lean_Xml_Parser_quote___rarg___closed__3;
x_3 = x_36;
x_4 = x_43;
goto block_26;
}
else
{
lean_dec(x_36);
lean_dec(x_1);
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_34, 0);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_34);
x_46 = l_String_Iterator_hasNext(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_45);
x_47 = l_Lean_Parsec_unexpectedEndOfInput;
x_3 = x_44;
x_4 = x_47;
goto block_26;
}
else
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; 
lean_inc(x_44);
x_48 = l_String_Iterator_next(x_44);
x_49 = l_String_Iterator_curr(x_44);
x_50 = x_49 == x_2;
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_48);
lean_dec(x_45);
x_51 = l_Lean_Xml_Parser_quote___rarg___closed__3;
x_3 = x_44;
x_4 = x_51;
goto block_26;
}
else
{
lean_object* x_52; 
lean_dec(x_44);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_34, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_dec(x_34);
x_3 = x_53;
x_4 = x_54;
goto block_26;
}
}
}
block_26:
{
uint8_t x_5; 
x_5 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = 39;
x_8 = l_String_Iterator_hasNext(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Parsec_unexpectedEndOfInput;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_String_Iterator_next(x_1);
x_12 = l_String_Iterator_curr(x_1);
x_13 = x_12 == x_7;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = l_Lean_Xml_Parser_quote___rarg___closed__6;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = l_Lean_Xml_Parser_SystemLiteral___closed__2;
x_17 = l_Lean_Parsec_manyChars(x_16, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_SystemLiteral___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Lean_Xml_Parser_SystemLiteral___lambda__1(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PubidChar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-'()+,./:=?;!*#@$_%");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PubidChar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PublidChar expected");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PubidChar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_56; 
x_56 = l_String_Iterator_hasNext(x_1);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_57;
goto block_55;
}
else
{
lean_object* x_58; uint32_t x_59; uint32_t x_60; uint8_t x_61; 
lean_inc(x_1);
x_58 = l_String_Iterator_next(x_1);
x_59 = l_String_Iterator_curr(x_1);
x_60 = 65;
x_61 = x_60 <= x_59;
if (x_61 == 0)
{
uint32_t x_62; uint8_t x_63; 
x_62 = 97;
x_63 = x_62 <= x_59;
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_58);
x_64 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_64;
goto block_55;
}
else
{
uint32_t x_65; uint8_t x_66; 
x_65 = 122;
x_66 = x_59 <= x_65;
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_58);
x_67 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_67;
goto block_55;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_1);
x_68 = lean_box_uint32(x_59);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint32_t x_70; uint8_t x_71; 
x_70 = 90;
x_71 = x_59 <= x_70;
if (x_71 == 0)
{
uint32_t x_72; uint8_t x_73; 
x_72 = 97;
x_73 = x_72 <= x_59;
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_58);
x_74 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_74;
goto block_55;
}
else
{
uint32_t x_75; uint8_t x_76; 
x_75 = 122;
x_76 = x_59 <= x_75;
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_58);
x_77 = l_Lean_Xml_Parser_EncName___lambda__1___closed__4;
lean_inc(x_1);
x_2 = x_1;
x_3 = x_77;
goto block_55;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_78 = lean_box_uint32(x_59);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_58);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_1);
x_80 = lean_box_uint32(x_59);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_58);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
block_55:
{
uint8_t x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_43; 
lean_dec(x_3);
lean_dec(x_2);
x_43 = l_String_Iterator_hasNext(x_1);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_6 = x_1;
x_7 = x_44;
goto block_42;
}
else
{
lean_object* x_45; uint32_t x_46; uint32_t x_47; uint8_t x_48; 
lean_inc(x_1);
x_45 = l_String_Iterator_next(x_1);
x_46 = l_String_Iterator_curr(x_1);
x_47 = 48;
x_48 = x_47 <= x_46;
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_45);
x_49 = l_Lean_Xml_Parser_NameChar___closed__11;
lean_inc(x_1);
x_6 = x_1;
x_7 = x_49;
goto block_42;
}
else
{
uint32_t x_50; uint8_t x_51; 
x_50 = 57;
x_51 = x_46 <= x_50;
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_45);
x_52 = l_Lean_Xml_Parser_NameChar___closed__11;
lean_inc(x_1);
x_6 = x_1;
x_7 = x_52;
goto block_42;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = lean_box_uint32(x_46);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
block_42:
{
uint8_t x_8; 
x_8 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_10 = l_Lean_Xml_Parser_endl(x_1);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_16);
if (x_18 == 0)
{
lean_dec(x_1);
return x_10;
}
else
{
uint8_t x_19; 
lean_dec(x_17);
lean_dec(x_16);
x_19 = l_String_Iterator_hasNext(x_1);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_21; uint32_t x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_1);
x_21 = l_String_Iterator_next(x_1);
x_22 = l_String_Iterator_curr(x_1);
x_23 = l_Lean_Xml_Parser_PubidChar___closed__1;
x_24 = l_String_contains(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
x_25 = l_Lean_Xml_Parser_PubidChar___closed__2;
lean_ctor_set(x_10, 1, x_25);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_box_uint32(x_22);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_26);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_28);
lean_dec(x_27);
x_31 = l_String_Iterator_hasNext(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Parsec_unexpectedEndOfInput;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; uint32_t x_35; lean_object* x_36; uint8_t x_37; 
lean_inc(x_1);
x_34 = l_String_Iterator_next(x_1);
x_35 = l_String_Iterator_curr(x_1);
x_36 = l_Lean_Xml_Parser_PubidChar___closed__1;
x_37 = l_String_contains(x_36, x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
x_38 = l_Lean_Xml_Parser_PubidChar___closed__2;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_40 = lean_box_uint32(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_PubidLiteral___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'\\'' not expected");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PubidLiteral___lambda__1(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Xml_Parser_PubidChar(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_unbox_uint32(x_5);
x_7 = x_6 == x_1;
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = l_Lean_Xml_Parser_PubidLiteral___lambda__1___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_8);
return x_3;
}
}
else
{
lean_object* x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_unbox_uint32(x_10);
x_12 = x_11 == x_1;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_14 = l_Lean_Xml_Parser_PubidLiteral___lambda__1___closed__1;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_PubidLiteral___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 39;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PubidLiteral___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_PubidLiteral___closed__1___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_PubidLiteral___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PubidLiteral___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_PubidLiteral___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_attempt___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PubidLiteral___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_PubidChar), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PubidLiteral(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_43; 
x_2 = 34;
x_43 = l_String_Iterator_hasNext(x_1);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_3 = x_1;
x_4 = x_44;
goto block_42;
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
lean_inc(x_1);
x_45 = l_String_Iterator_next(x_1);
x_46 = l_String_Iterator_curr(x_1);
x_47 = x_46 == x_2;
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_45);
x_48 = l_Lean_Xml_Parser_quote___rarg___closed__3;
lean_inc(x_1);
x_3 = x_1;
x_4 = x_48;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_Xml_Parser_PubidLiteral___closed__3;
x_50 = l_Lean_Parsec_manyChars(x_49, x_45);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = l_String_Iterator_hasNext(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_free_object(x_50);
lean_dec(x_53);
x_55 = l_Lean_Parsec_unexpectedEndOfInput;
x_3 = x_52;
x_4 = x_55;
goto block_42;
}
else
{
lean_object* x_56; uint32_t x_57; uint8_t x_58; 
lean_inc(x_52);
x_56 = l_String_Iterator_next(x_52);
x_57 = l_String_Iterator_curr(x_52);
x_58 = x_57 == x_2;
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_56);
lean_free_object(x_50);
lean_dec(x_53);
x_59 = l_Lean_Xml_Parser_quote___rarg___closed__3;
x_3 = x_52;
x_4 = x_59;
goto block_42;
}
else
{
lean_dec(x_52);
lean_dec(x_1);
lean_ctor_set(x_50, 0, x_56);
return x_50;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_50, 0);
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_50);
x_62 = l_String_Iterator_hasNext(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_61);
x_63 = l_Lean_Parsec_unexpectedEndOfInput;
x_3 = x_60;
x_4 = x_63;
goto block_42;
}
else
{
lean_object* x_64; uint32_t x_65; uint8_t x_66; 
lean_inc(x_60);
x_64 = l_String_Iterator_next(x_60);
x_65 = l_String_Iterator_curr(x_60);
x_66 = x_65 == x_2;
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_64);
lean_dec(x_61);
x_67 = l_Lean_Xml_Parser_quote___rarg___closed__3;
x_3 = x_60;
x_4 = x_67;
goto block_42;
}
else
{
lean_object* x_68; 
lean_dec(x_60);
lean_dec(x_1);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_61);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_50, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_50, 1);
lean_inc(x_70);
lean_dec(x_50);
x_3 = x_69;
x_4 = x_70;
goto block_42;
}
}
}
block_42:
{
uint8_t x_5; 
x_5 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
uint32_t x_7; uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = 39;
x_8 = l_String_Iterator_hasNext(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Parsec_unexpectedEndOfInput;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_String_Iterator_next(x_1);
x_12 = l_String_Iterator_curr(x_1);
x_13 = x_12 == x_7;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = l_Lean_Xml_Parser_quote___rarg___closed__6;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = l_Lean_Xml_Parser_PubidLiteral___closed__2;
x_17 = l_Lean_Parsec_manyChars(x_16, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_String_Iterator_hasNext(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
x_22 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_22);
return x_17;
}
else
{
lean_object* x_23; uint32_t x_24; uint8_t x_25; 
lean_inc(x_19);
x_23 = l_String_Iterator_next(x_19);
x_24 = l_String_Iterator_curr(x_19);
x_25 = x_24 == x_7;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_20);
x_26 = l_Lean_Xml_Parser_quote___rarg___closed__6;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_26);
return x_17;
}
else
{
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = l_String_Iterator_hasNext(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
x_30 = l_Lean_Parsec_unexpectedEndOfInput;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; uint32_t x_33; uint8_t x_34; 
lean_inc(x_27);
x_32 = l_String_Iterator_next(x_27);
x_33 = l_String_Iterator_curr(x_27);
x_34 = x_33 == x_7;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_28);
x_35 = l_Lean_Xml_Parser_quote___rarg___closed__6;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_28);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PubidLiteral___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Xml_Parser_PubidLiteral___lambda__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Xml_Parser_ExternalID___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("SYSTEM");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_ExternalID___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PUBLIC");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_ExternalID(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_ExternalID___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Xml_Parser_S(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Xml_Parser_SystemLiteral(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_7, 1, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
x_17 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_15);
if (x_17 == 0)
{
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_7);
lean_dec(x_16);
lean_dec(x_15);
x_18 = l_Lean_Xml_Parser_ExternalID___closed__2;
x_19 = l_Lean_Parsec_pstring(x_18, x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Xml_Parser_S(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Xml_Parser_PubidLiteral(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Xml_Parser_S(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Xml_Parser_SystemLiteral(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 1, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_21);
if (x_46 == 0)
{
return x_21;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_21, 0);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_21);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_19);
if (x_50 == 0)
{
return x_19;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_19, 0);
x_52 = lean_ctor_get(x_19, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_19);
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
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_1);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_54);
x_58 = l_Lean_Xml_Parser_ExternalID___closed__2;
x_59 = l_Lean_Parsec_pstring(x_58, x_1);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Xml_Parser_S(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Xml_Parser_PubidLiteral(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_Xml_Parser_S(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Xml_Parser_SystemLiteral(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
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
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_65, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_78 = x_65;
} else {
 lean_dec_ref(x_65);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_63, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_63, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_82 = x_63;
} else {
 lean_dec_ref(x_63);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_61, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_61, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_86 = x_61;
} else {
 lean_dec_ref(x_61);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_59, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_59, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_90 = x_59;
} else {
 lean_dec_ref(x_59);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_5);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_93);
if (x_95 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_free_object(x_5);
lean_dec(x_94);
lean_dec(x_93);
x_96 = l_Lean_Xml_Parser_ExternalID___closed__2;
x_97 = l_Lean_Parsec_pstring(x_96, x_1);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l_Lean_Xml_Parser_S(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l_Lean_Xml_Parser_PubidLiteral(x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_Xml_Parser_S(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l_Lean_Xml_Parser_SystemLiteral(x_104);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 1);
lean_dec(x_107);
x_108 = lean_box(0);
lean_ctor_set(x_105, 1, x_108);
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
lean_dec(x_105);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_105);
if (x_112 == 0)
{
return x_105;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_105, 0);
x_114 = lean_ctor_get(x_105, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_105);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_103);
if (x_116 == 0)
{
return x_103;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_103, 0);
x_118 = lean_ctor_get(x_103, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_103);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_101);
if (x_120 == 0)
{
return x_101;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_101, 0);
x_122 = lean_ctor_get(x_101, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_101);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_99);
if (x_124 == 0)
{
return x_99;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_99, 0);
x_126 = lean_ctor_get(x_99, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_99);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_97);
if (x_128 == 0)
{
return x_97;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_97, 0);
x_130 = lean_ctor_get(x_97, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_97);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_5, 0);
x_133 = lean_ctor_get(x_5, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_5);
x_134 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_132);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_1);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_133);
lean_dec(x_132);
x_136 = l_Lean_Xml_Parser_ExternalID___closed__2;
x_137 = l_Lean_Parsec_pstring(x_136, x_1);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
x_139 = l_Lean_Xml_Parser_S(x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lean_Xml_Parser_PubidLiteral(x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec(x_141);
x_143 = l_Lean_Xml_Parser_S(x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec(x_143);
x_145 = l_Lean_Xml_Parser_SystemLiteral(x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
x_148 = lean_box(0);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_145, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_145, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_152 = x_145;
} else {
 lean_dec_ref(x_145);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_143, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_143, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_156 = x_143;
} else {
 lean_dec_ref(x_143);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_141, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_141, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_160 = x_141;
} else {
 lean_dec_ref(x_141);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_139, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_139, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_164 = x_139;
} else {
 lean_dec_ref(x_139);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_137, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_137, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_168 = x_137;
} else {
 lean_dec_ref(x_137);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
}
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_3);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_3, 0);
x_172 = lean_ctor_get(x_3, 1);
x_173 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_171);
if (x_173 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_free_object(x_3);
lean_dec(x_172);
lean_dec(x_171);
x_174 = l_Lean_Xml_Parser_ExternalID___closed__2;
x_175 = l_Lean_Parsec_pstring(x_174, x_1);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec(x_175);
x_177 = l_Lean_Xml_Parser_S(x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec(x_177);
x_179 = l_Lean_Xml_Parser_PubidLiteral(x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec(x_179);
x_181 = l_Lean_Xml_Parser_S(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l_Lean_Xml_Parser_SystemLiteral(x_182);
if (lean_obj_tag(x_183) == 0)
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_183, 1);
lean_dec(x_185);
x_186 = lean_box(0);
lean_ctor_set(x_183, 1, x_186);
return x_183;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
else
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_183);
if (x_190 == 0)
{
return x_183;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_183, 0);
x_192 = lean_ctor_get(x_183, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_183);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_181);
if (x_194 == 0)
{
return x_181;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_181, 0);
x_196 = lean_ctor_get(x_181, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_181);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_179);
if (x_198 == 0)
{
return x_179;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_179, 0);
x_200 = lean_ctor_get(x_179, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_179);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_177);
if (x_202 == 0)
{
return x_177;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_177, 0);
x_204 = lean_ctor_get(x_177, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_177);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_175);
if (x_206 == 0)
{
return x_175;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_175, 0);
x_208 = lean_ctor_get(x_175, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_175);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = lean_ctor_get(x_3, 0);
x_211 = lean_ctor_get(x_3, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_3);
x_212 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_210);
if (x_212 == 0)
{
lean_object* x_213; 
lean_dec(x_1);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_211);
lean_dec(x_210);
x_214 = l_Lean_Xml_Parser_ExternalID___closed__2;
x_215 = l_Lean_Parsec_pstring(x_214, x_1);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec(x_215);
x_217 = l_Lean_Xml_Parser_S(x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec(x_217);
x_219 = l_Lean_Xml_Parser_PubidLiteral(x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec(x_219);
x_221 = l_Lean_Xml_Parser_S(x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec(x_221);
x_223 = l_Lean_Xml_Parser_SystemLiteral(x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_225 = x_223;
} else {
 lean_dec_ref(x_223);
 x_225 = lean_box(0);
}
x_226 = lean_box(0);
if (lean_is_scalar(x_225)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_225;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_223, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_223, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_230 = x_223;
} else {
 lean_dec_ref(x_223);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_221, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_221, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_234 = x_221;
} else {
 lean_dec_ref(x_221);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_219, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_219, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_238 = x_219;
} else {
 lean_dec_ref(x_219);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_240 = lean_ctor_get(x_217, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_217, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_242 = x_217;
} else {
 lean_dec_ref(x_217);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_215, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_215, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_246 = x_215;
} else {
 lean_dec_ref(x_215);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___lambda__1___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 124;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_Mixed___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_Mixed___lambda__1___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Mixed___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_26; 
lean_inc(x_1);
x_26 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_2 = x_27;
goto block_25;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_29);
if (x_31 == 0)
{
lean_dec(x_1);
return x_26;
}
else
{
lean_free_object(x_26);
lean_dec(x_30);
lean_dec(x_29);
x_2 = x_1;
goto block_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_dec(x_33);
lean_dec(x_32);
x_2 = x_1;
goto block_25;
}
}
}
block_25:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 124;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_Mixed___lambda__1___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_inc(x_7);
x_12 = l_Lean_Xml_Parser_S(x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Xml_Parser_Name(x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_7, x_16);
if (x_18 == 0)
{
lean_dec(x_7);
return x_12;
}
else
{
lean_object* x_19; 
lean_free_object(x_12);
lean_dec(x_17);
lean_dec(x_16);
x_19 = l_Lean_Xml_Parser_Name(x_7);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_7, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
x_24 = l_Lean_Xml_Parser_Name(x_7);
return x_24;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 41;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_Mixed___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_Mixed___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#PCDATA");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___closed__5() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 40;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_Mixed___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_Mixed___closed__6;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_Mixed___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_Mixed___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")*");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Mixed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_15; uint32_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_61; uint8_t x_94; 
x_37 = 40;
x_94 = l_String_Iterator_hasNext(x_1);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_38 = x_1;
x_39 = x_95;
goto block_60;
}
else
{
lean_object* x_96; uint32_t x_97; uint8_t x_98; 
lean_inc(x_1);
x_96 = l_String_Iterator_next(x_1);
x_97 = l_String_Iterator_curr(x_1);
x_98 = x_97 == x_37;
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_96);
x_99 = l_Lean_Xml_Parser_Mixed___closed__7;
lean_inc(x_1);
x_38 = x_1;
x_39 = x_99;
goto block_60;
}
else
{
lean_object* x_100; 
lean_inc(x_96);
x_100 = l_Lean_Xml_Parser_S(x_96);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_96);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_Xml_Parser_Mixed___closed__4;
x_103 = l_Lean_Parsec_pstring(x_102, x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_61 = x_104;
goto block_93;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_38 = x_105;
x_39 = x_106;
goto block_60;
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_100, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_100, 1);
lean_inc(x_108);
lean_dec(x_100);
x_109 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_96, x_107);
if (x_109 == 0)
{
lean_dec(x_96);
x_38 = x_107;
x_39 = x_108;
goto block_60;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_108);
lean_dec(x_107);
x_110 = l_Lean_Xml_Parser_Mixed___closed__4;
x_111 = l_Lean_Parsec_pstring(x_110, x_96);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_61 = x_112;
goto block_93;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_38 = x_113;
x_39 = x_114;
goto block_60;
}
}
}
}
}
block_14:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 41;
x_5 = l_String_Iterator_hasNext(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = l_Lean_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; 
lean_inc(x_2);
x_8 = l_String_Iterator_next(x_2);
x_9 = l_String_Iterator_curr(x_2);
x_10 = x_9 == x_4;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
x_11 = l_Lean_Xml_Parser_Mixed___closed__3;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
block_36:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Xml_Parser_Mixed___closed__4;
x_17 = l_Lean_Parsec_pstring(x_16, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_18);
x_19 = l_Lean_Xml_Parser_S(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_2 = x_20;
x_3 = x_21;
goto block_14;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
x_25 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_18, x_23);
if (x_25 == 0)
{
lean_dec(x_18);
return x_19;
}
else
{
lean_object* x_26; 
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_box(0);
x_2 = x_18;
x_3 = x_26;
goto block_14;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_18, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_27);
x_31 = lean_box(0);
x_2 = x_18;
x_3 = x_31;
goto block_14;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
block_60:
{
uint8_t x_40; 
x_40 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_1);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_39);
lean_dec(x_38);
x_42 = l_String_Iterator_hasNext(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Parsec_unexpectedEndOfInput;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
lean_inc(x_1);
x_45 = l_String_Iterator_next(x_1);
x_46 = l_String_Iterator_curr(x_1);
x_47 = x_46 == x_37;
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
x_48 = l_Lean_Xml_Parser_Mixed___closed__7;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_1);
lean_inc(x_45);
x_50 = l_Lean_Xml_Parser_S(x_45);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec(x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_15 = x_51;
goto block_36;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 1);
x_55 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_45, x_53);
if (x_55 == 0)
{
lean_dec(x_45);
return x_50;
}
else
{
lean_free_object(x_50);
lean_dec(x_54);
lean_dec(x_53);
x_15 = x_45;
goto block_36;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_45, x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_45);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
x_15 = x_45;
goto block_36;
}
}
}
}
}
}
}
block_93:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = l_Lean_Xml_Parser_Mixed___closed__8;
x_63 = l_Lean_Parsec_many(lean_box(0));
x_64 = lean_apply_2(x_63, x_62, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
lean_inc(x_65);
x_66 = l_Lean_Xml_Parser_S(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Xml_Parser_Mixed___closed__9;
x_69 = l_Lean_Parsec_pstring(x_68, x_67);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 1);
lean_dec(x_71);
x_72 = lean_box(0);
lean_ctor_set(x_69, 1, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_dec(x_69);
x_38 = x_76;
x_39 = x_77;
goto block_60;
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_66, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
lean_dec(x_66);
x_80 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_65, x_78);
if (x_80 == 0)
{
lean_dec(x_65);
x_38 = x_78;
x_39 = x_79;
goto block_60;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_79);
lean_dec(x_78);
x_81 = l_Lean_Xml_Parser_Mixed___closed__9;
x_82 = l_Lean_Parsec_pstring(x_81, x_65);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 1);
lean_dec(x_84);
x_85 = lean_box(0);
lean_ctor_set(x_82, 1, x_85);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
lean_dec(x_82);
x_38 = x_89;
x_39 = x_90;
goto block_60;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_64, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_64, 1);
lean_inc(x_92);
lean_dec(x_64);
x_38 = x_91;
x_39 = x_92;
goto block_60;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_cp___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 43;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_cp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_cp___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_cp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_cp___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_cp___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 42;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_cp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_cp___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_cp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_cp___closed__5;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_cp___closed__7() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 63;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_cp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_cp___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_cp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_cp___closed__8;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_cp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_45; 
lean_inc(x_1);
x_45 = l_Lean_Xml_Parser_Name(x_1);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_2 = x_46;
x_3 = x_47;
goto block_44;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
x_51 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_49);
if (x_51 == 0)
{
lean_dec(x_1);
return x_45;
}
else
{
lean_object* x_52; 
lean_free_object(x_45);
lean_dec(x_50);
lean_dec(x_49);
lean_inc(x_1);
x_52 = l_Lean_Xml_Parser_choice(x_1);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_2 = x_53;
x_3 = x_54;
goto block_44;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
x_58 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_56);
if (x_58 == 0)
{
lean_dec(x_1);
return x_52;
}
else
{
lean_object* x_59; 
lean_free_object(x_52);
lean_dec(x_57);
lean_dec(x_56);
x_59 = l_Lean_Xml_Parser_seq(x_1);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_2 = x_60;
x_3 = x_61;
goto block_44;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_52, 0);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_52);
x_68 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_66);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_1);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; 
lean_dec(x_67);
lean_dec(x_66);
x_70 = l_Lean_Xml_Parser_seq(x_1);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_2 = x_71;
x_3 = x_72;
goto block_44;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_75 = x_70;
} else {
 lean_dec_ref(x_70);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_45, 0);
x_78 = lean_ctor_get(x_45, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_45);
x_79 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_77);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_1);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; 
lean_dec(x_78);
lean_dec(x_77);
lean_inc(x_1);
x_81 = l_Lean_Xml_Parser_choice(x_1);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_1);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_2 = x_82;
x_3 = x_83;
goto block_44;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
x_87 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_84);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_1);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
x_89 = l_Lean_Xml_Parser_seq(x_1);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_2 = x_90;
x_3 = x_91;
goto block_44;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_94 = x_89;
} else {
 lean_dec_ref(x_89);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
}
}
block_44:
{
lean_object* x_4; lean_object* x_5; lean_object* x_23; lean_object* x_24; uint32_t x_36; uint8_t x_37; 
x_36 = 63;
x_37 = l_String_Iterator_hasNext(x_2);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_2);
x_23 = x_2;
x_24 = x_38;
goto block_35;
}
else
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; 
lean_inc(x_2);
x_39 = l_String_Iterator_next(x_2);
x_40 = l_String_Iterator_curr(x_2);
x_41 = x_40 == x_36;
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
x_42 = l_Lean_Xml_Parser_cp___closed__9;
lean_inc(x_2);
x_23 = x_2;
x_24 = x_42;
goto block_35;
}
else
{
lean_object* x_43; 
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
}
block_22:
{
uint8_t x_6; 
x_6 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 43;
x_9 = l_String_Iterator_hasNext(x_2);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_11 = l_Lean_Parsec_unexpectedEndOfInput;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
else
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
lean_inc(x_2);
x_14 = l_String_Iterator_next(x_2);
x_15 = l_String_Iterator_curr(x_2);
x_16 = x_15 == x_8;
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = l_Lean_Xml_Parser_cp___closed__3;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
}
block_35:
{
uint8_t x_25; 
x_25 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
else
{
uint32_t x_27; uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_23);
x_27 = 42;
x_28 = l_String_Iterator_hasNext(x_2);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_2);
x_4 = x_2;
x_5 = x_29;
goto block_22;
}
else
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
lean_inc(x_2);
x_30 = l_String_Iterator_next(x_2);
x_31 = l_String_Iterator_curr(x_2);
x_32 = x_31 == x_27;
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
x_33 = l_Lean_Xml_Parser_cp___closed__6;
lean_inc(x_2);
x_4 = x_2;
x_5 = x_33;
goto block_22;
}
else
{
lean_object* x_34; 
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_seq___lambda__1___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 44;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_seq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_seq___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_seq___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_seq___lambda__1___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_seq___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_26; 
lean_inc(x_1);
x_26 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_2 = x_27;
goto block_25;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_29);
if (x_31 == 0)
{
lean_dec(x_1);
return x_26;
}
else
{
lean_free_object(x_26);
lean_dec(x_30);
lean_dec(x_29);
x_2 = x_1;
goto block_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_dec(x_33);
lean_dec(x_32);
x_2 = x_1;
goto block_25;
}
}
}
block_25:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 44;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_seq___lambda__1___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_inc(x_7);
x_12 = l_Lean_Xml_Parser_S(x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Xml_Parser_cp(x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_7, x_16);
if (x_18 == 0)
{
lean_dec(x_7);
return x_12;
}
else
{
lean_object* x_19; 
lean_free_object(x_12);
lean_dec(x_17);
lean_dec(x_16);
x_19 = l_Lean_Xml_Parser_cp(x_7);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_7, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
x_24 = l_Lean_Xml_Parser_cp(x_7);
return x_24;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_seq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_seq___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_seq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; uint32_t x_41; uint8_t x_42; 
x_41 = 40;
x_42 = l_String_Iterator_hasNext(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Parsec_unexpectedEndOfInput;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
lean_inc(x_1);
x_45 = l_String_Iterator_next(x_1);
x_46 = l_String_Iterator_curr(x_1);
x_47 = x_46 == x_41;
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
x_48 = l_Lean_Xml_Parser_Mixed___closed__7;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_1);
lean_inc(x_45);
x_50 = l_Lean_Xml_Parser_S(x_45);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec(x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_15 = x_51;
goto block_40;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 1);
x_55 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_45, x_53);
if (x_55 == 0)
{
lean_dec(x_45);
return x_50;
}
else
{
lean_free_object(x_50);
lean_dec(x_54);
lean_dec(x_53);
x_15 = x_45;
goto block_40;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_45, x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_45);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
x_15 = x_45;
goto block_40;
}
}
}
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 41;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_Mixed___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
block_40:
{
lean_object* x_16; 
x_16 = l_Lean_Xml_Parser_cp(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Xml_Parser_seq___closed__1;
x_19 = l_Lean_Parsec_many(lean_box(0));
x_20 = lean_apply_2(x_19, x_18, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_21);
x_22 = l_Lean_Xml_Parser_S(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_2 = x_23;
goto block_14;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_21, x_25);
if (x_27 == 0)
{
lean_dec(x_21);
return x_22;
}
else
{
lean_free_object(x_22);
lean_dec(x_26);
lean_dec(x_25);
x_2 = x_21;
goto block_14;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_21, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
x_2 = x_21;
goto block_14;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_choice___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_26; 
lean_inc(x_1);
x_26 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_2 = x_27;
goto block_25;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_29);
if (x_31 == 0)
{
lean_dec(x_1);
return x_26;
}
else
{
lean_free_object(x_26);
lean_dec(x_30);
lean_dec(x_29);
x_2 = x_1;
goto block_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_dec(x_33);
lean_dec(x_32);
x_2 = x_1;
goto block_25;
}
}
}
block_25:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 124;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_Mixed___lambda__1___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_inc(x_7);
x_12 = l_Lean_Xml_Parser_S(x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Xml_Parser_cp(x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_7, x_16);
if (x_18 == 0)
{
lean_dec(x_7);
return x_12;
}
else
{
lean_object* x_19; 
lean_free_object(x_12);
lean_dec(x_17);
lean_dec(x_16);
x_19 = l_Lean_Xml_Parser_cp(x_7);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_7, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
x_24 = l_Lean_Xml_Parser_cp(x_7);
return x_24;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_choice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_choice___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_choice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; uint32_t x_41; uint8_t x_42; 
x_41 = 40;
x_42 = l_String_Iterator_hasNext(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Parsec_unexpectedEndOfInput;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
lean_inc(x_1);
x_45 = l_String_Iterator_next(x_1);
x_46 = l_String_Iterator_curr(x_1);
x_47 = x_46 == x_41;
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
x_48 = l_Lean_Xml_Parser_Mixed___closed__7;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_1);
lean_inc(x_45);
x_50 = l_Lean_Xml_Parser_S(x_45);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec(x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_15 = x_51;
goto block_40;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 1);
x_55 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_45, x_53);
if (x_55 == 0)
{
lean_dec(x_45);
return x_50;
}
else
{
lean_free_object(x_50);
lean_dec(x_54);
lean_dec(x_53);
x_15 = x_45;
goto block_40;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_45, x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_45);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
x_15 = x_45;
goto block_40;
}
}
}
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 41;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_Mixed___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
block_40:
{
lean_object* x_16; 
x_16 = l_Lean_Xml_Parser_cp(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Xml_Parser_choice___closed__1;
x_19 = l_Lean_Parsec_many1(lean_box(0));
x_20 = lean_apply_2(x_19, x_18, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_21);
x_22 = l_Lean_Xml_Parser_S(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_2 = x_23;
goto block_14;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_21, x_25);
if (x_27 == 0)
{
lean_dec(x_21);
return x_22;
}
else
{
lean_free_object(x_22);
lean_dec(x_26);
lean_dec(x_25);
x_2 = x_21;
goto block_14;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_21, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
x_2 = x_21;
goto block_14;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_children(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_45; 
lean_inc(x_1);
x_45 = l_Lean_Xml_Parser_choice(x_1);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_2 = x_46;
x_3 = x_47;
goto block_44;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
x_51 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_49);
if (x_51 == 0)
{
lean_dec(x_1);
return x_45;
}
else
{
lean_object* x_52; 
lean_free_object(x_45);
lean_dec(x_50);
lean_dec(x_49);
x_52 = l_Lean_Xml_Parser_seq(x_1);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_2 = x_53;
x_3 = x_54;
goto block_44;
}
else
{
uint8_t x_55; 
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
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_1);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_60);
lean_dec(x_59);
x_63 = l_Lean_Xml_Parser_seq(x_1);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_2 = x_64;
x_3 = x_65;
goto block_44;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_68 = x_63;
} else {
 lean_dec_ref(x_63);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
block_44:
{
lean_object* x_4; lean_object* x_5; lean_object* x_23; lean_object* x_24; uint32_t x_36; uint8_t x_37; 
x_36 = 63;
x_37 = l_String_Iterator_hasNext(x_2);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_2);
x_23 = x_2;
x_24 = x_38;
goto block_35;
}
else
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; 
lean_inc(x_2);
x_39 = l_String_Iterator_next(x_2);
x_40 = l_String_Iterator_curr(x_2);
x_41 = x_40 == x_36;
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
x_42 = l_Lean_Xml_Parser_cp___closed__9;
lean_inc(x_2);
x_23 = x_2;
x_24 = x_42;
goto block_35;
}
else
{
lean_object* x_43; 
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_3);
return x_43;
}
}
block_22:
{
uint8_t x_6; 
x_6 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint32_t x_8; uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 43;
x_9 = l_String_Iterator_hasNext(x_2);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_11 = l_Lean_Parsec_unexpectedEndOfInput;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
else
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
lean_inc(x_2);
x_14 = l_String_Iterator_next(x_2);
x_15 = l_String_Iterator_curr(x_2);
x_16 = x_15 == x_8;
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = l_Lean_Xml_Parser_cp___closed__3;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
}
block_35:
{
uint8_t x_25; 
x_25 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
else
{
uint32_t x_27; uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_23);
x_27 = 42;
x_28 = l_String_Iterator_hasNext(x_2);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_2);
x_4 = x_2;
x_5 = x_29;
goto block_22;
}
else
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
lean_inc(x_2);
x_30 = l_String_Iterator_next(x_2);
x_31 = l_String_Iterator_curr(x_2);
x_32 = x_31 == x_27;
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
x_33 = l_Lean_Xml_Parser_cp___closed__6;
lean_inc(x_2);
x_4 = x_2;
x_5 = x_33;
goto block_22;
}
else
{
lean_object* x_34; 
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_contentspec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("EMPTY");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_contentspec___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ANY");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_contentspec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_contentspec___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_11);
if (x_13 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_3);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_Lean_Xml_Parser_contentspec___closed__2;
lean_inc(x_1);
x_15 = l_Lean_Parsec_pstring(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 1, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_23);
if (x_25 == 0)
{
lean_dec(x_1);
return x_15;
}
else
{
lean_object* x_26; 
lean_free_object(x_15);
lean_dec(x_24);
lean_dec(x_23);
lean_inc(x_1);
x_26 = l_Lean_Xml_Parser_Mixed(x_1);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
x_34 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_32);
if (x_34 == 0)
{
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_35; 
lean_free_object(x_26);
lean_dec(x_33);
lean_dec(x_32);
x_35 = l_Lean_Xml_Parser_children(x_1);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_26);
x_38 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_1);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_36);
x_40 = l_Lean_Xml_Parser_children(x_1);
return x_40;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_1);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_41);
lean_inc(x_1);
x_45 = l_Lean_Xml_Parser_Mixed(x_1);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_52 = x_45;
} else {
 lean_dec_ref(x_45);
 x_52 = lean_box(0);
}
x_53 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_50);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_1);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_55 = l_Lean_Xml_Parser_children(x_1);
return x_55;
}
}
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_3, 0);
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_3);
x_58 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_1);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_57);
lean_dec(x_56);
x_60 = l_Lean_Xml_Parser_contentspec___closed__2;
lean_inc(x_1);
x_61 = l_Lean_Parsec_pstring(x_60, x_1);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
x_69 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_66);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_1);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_inc(x_1);
x_71 = l_Lean_Xml_Parser_Mixed(x_1);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_1);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_78 = x_71;
} else {
 lean_dec_ref(x_71);
 x_78 = lean_box(0);
}
x_79 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_76);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_1);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
else
{
lean_object* x_81; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
x_81 = l_Lean_Xml_Parser_children(x_1);
return x_81;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_elementDecl___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 62;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_elementDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_elementDecl___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_elementDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_elementDecl___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_elementDecl___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<!ELEMENT");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_elementDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Xml_Parser_elementDecl___closed__4;
x_16 = l_Lean_Parsec_pstring(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Xml_Parser_S(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Xml_Parser_Name(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Xml_Parser_contentspec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_23);
x_24 = l_Lean_Xml_Parser_S(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_2 = x_25;
goto block_14;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
x_29 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_23, x_27);
if (x_29 == 0)
{
lean_dec(x_23);
return x_24;
}
else
{
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_27);
x_2 = x_23;
goto block_14;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_23, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_dec(x_31);
lean_dec(x_30);
x_2 = x_23;
goto block_14;
}
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
return x_16;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 62;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_elementDecl___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_StringType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CDATA");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_StringType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_StringType___closed__1;
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_TokenizedType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ID");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_TokenizedType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IDREF");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_TokenizedType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IDREFS");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_TokenizedType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ENTITY");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_TokenizedType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ENTITIES");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_TokenizedType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("NMTOKEN");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_TokenizedType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("NMTOKENS");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_TokenizedType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_TokenizedType___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_11);
if (x_13 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_3);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_Lean_Xml_Parser_TokenizedType___closed__2;
lean_inc(x_1);
x_15 = l_Lean_Parsec_pstring(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 1, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_23);
if (x_25 == 0)
{
lean_dec(x_1);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
lean_dec(x_24);
lean_dec(x_23);
x_26 = l_Lean_Xml_Parser_TokenizedType___closed__3;
lean_inc(x_1);
x_27 = l_Lean_Parsec_pstring(x_26, x_1);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 1, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
x_37 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_35);
if (x_37 == 0)
{
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_27);
lean_dec(x_36);
lean_dec(x_35);
x_38 = l_Lean_Xml_Parser_TokenizedType___closed__4;
lean_inc(x_1);
x_39 = l_Lean_Parsec_pstring(x_38, x_1);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 1);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_39, 1, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
x_49 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_47);
if (x_49 == 0)
{
lean_dec(x_1);
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_free_object(x_39);
lean_dec(x_48);
lean_dec(x_47);
x_50 = l_Lean_Xml_Parser_TokenizedType___closed__5;
lean_inc(x_1);
x_51 = l_Lean_Parsec_pstring(x_50, x_1);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 1);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_51, 1, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
x_61 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_59);
if (x_61 == 0)
{
lean_dec(x_1);
return x_51;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_free_object(x_51);
lean_dec(x_60);
lean_dec(x_59);
x_62 = l_Lean_Xml_Parser_TokenizedType___closed__6;
lean_inc(x_1);
x_63 = l_Lean_Parsec_pstring(x_62, x_1);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 1);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_63, 1, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_63);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_63, 0);
x_72 = lean_ctor_get(x_63, 1);
x_73 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_71);
if (x_73 == 0)
{
lean_dec(x_1);
return x_63;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_free_object(x_63);
lean_dec(x_72);
lean_dec(x_71);
x_74 = l_Lean_Xml_Parser_TokenizedType___closed__7;
x_75 = l_Lean_Parsec_pstring(x_74, x_1);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 1);
lean_dec(x_77);
x_78 = lean_box(0);
lean_ctor_set(x_75, 1, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
return x_75;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_75, 0);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_75);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_63, 0);
x_87 = lean_ctor_get(x_63, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_63);
x_88 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_86);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_1);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_87);
lean_dec(x_86);
x_90 = l_Lean_Xml_Parser_TokenizedType___closed__7;
x_91 = l_Lean_Parsec_pstring(x_90, x_1);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
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
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_51, 0);
x_101 = lean_ctor_get(x_51, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_51);
x_102 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_100);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_1);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_101);
lean_dec(x_100);
x_104 = l_Lean_Xml_Parser_TokenizedType___closed__6;
lean_inc(x_1);
x_105 = l_Lean_Parsec_pstring(x_104, x_1);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_1);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
x_108 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_112 = x_105;
} else {
 lean_dec_ref(x_105);
 x_112 = lean_box(0);
}
x_113 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_110);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_1);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
x_115 = l_Lean_Xml_Parser_TokenizedType___closed__7;
x_116 = l_Lean_Parsec_pstring(x_115, x_1);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_123 = x_116;
} else {
 lean_dec_ref(x_116);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_39, 0);
x_126 = lean_ctor_get(x_39, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_39);
x_127 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_125);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_1);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_126);
lean_dec(x_125);
x_129 = l_Lean_Xml_Parser_TokenizedType___closed__5;
lean_inc(x_1);
x_130 = l_Lean_Parsec_pstring(x_129, x_1);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_1);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = lean_box(0);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_137 = x_130;
} else {
 lean_dec_ref(x_130);
 x_137 = lean_box(0);
}
x_138 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_135);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_1);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
x_140 = l_Lean_Xml_Parser_TokenizedType___closed__6;
lean_inc(x_1);
x_141 = l_Lean_Parsec_pstring(x_140, x_1);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_1);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_141, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_148 = x_141;
} else {
 lean_dec_ref(x_141);
 x_148 = lean_box(0);
}
x_149 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_146);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_1);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_146);
lean_ctor_set(x_150, 1, x_147);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
x_151 = l_Lean_Xml_Parser_TokenizedType___closed__7;
x_152 = l_Lean_Parsec_pstring(x_151, x_1);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
x_155 = lean_box(0);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_152, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_152, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_159 = x_152;
} else {
 lean_dec_ref(x_152);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_27, 0);
x_162 = lean_ctor_get(x_27, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_27);
x_163 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_161);
if (x_163 == 0)
{
lean_object* x_164; 
lean_dec(x_1);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_162);
lean_dec(x_161);
x_165 = l_Lean_Xml_Parser_TokenizedType___closed__4;
lean_inc(x_1);
x_166 = l_Lean_Parsec_pstring(x_165, x_1);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_1);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
x_169 = lean_box(0);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_171 = lean_ctor_get(x_166, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_166, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_173 = x_166;
} else {
 lean_dec_ref(x_166);
 x_173 = lean_box(0);
}
x_174 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_171);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_1);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_172);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
x_176 = l_Lean_Xml_Parser_TokenizedType___closed__5;
lean_inc(x_1);
x_177 = l_Lean_Parsec_pstring(x_176, x_1);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_1);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_182 = lean_ctor_get(x_177, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_177, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_184 = x_177;
} else {
 lean_dec_ref(x_177);
 x_184 = lean_box(0);
}
x_185 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_182);
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec(x_1);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_183);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
x_187 = l_Lean_Xml_Parser_TokenizedType___closed__6;
lean_inc(x_1);
x_188 = l_Lean_Parsec_pstring(x_187, x_1);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_1);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
x_191 = lean_box(0);
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_193 = lean_ctor_get(x_188, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_195 = x_188;
} else {
 lean_dec_ref(x_188);
 x_195 = lean_box(0);
}
x_196 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_193);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_1);
if (lean_is_scalar(x_195)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_195;
}
lean_ctor_set(x_197, 0, x_193);
lean_ctor_set(x_197, 1, x_194);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
x_198 = l_Lean_Xml_Parser_TokenizedType___closed__7;
x_199 = l_Lean_Parsec_pstring(x_198, x_1);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_201 = x_199;
} else {
 lean_dec_ref(x_199);
 x_201 = lean_box(0);
}
x_202 = lean_box(0);
if (lean_is_scalar(x_201)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_201;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_199, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_206 = x_199;
} else {
 lean_dec_ref(x_199);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_15, 0);
x_209 = lean_ctor_get(x_15, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_15);
x_210 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_208);
if (x_210 == 0)
{
lean_object* x_211; 
lean_dec(x_1);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_209);
lean_dec(x_208);
x_212 = l_Lean_Xml_Parser_TokenizedType___closed__3;
lean_inc(x_1);
x_213 = l_Lean_Parsec_pstring(x_212, x_1);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_1);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_215 = x_213;
} else {
 lean_dec_ref(x_213);
 x_215 = lean_box(0);
}
x_216 = lean_box(0);
if (lean_is_scalar(x_215)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_215;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_218 = lean_ctor_get(x_213, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_213, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_220 = x_213;
} else {
 lean_dec_ref(x_213);
 x_220 = lean_box(0);
}
x_221 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_218);
if (x_221 == 0)
{
lean_object* x_222; 
lean_dec(x_1);
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_220;
}
lean_ctor_set(x_222, 0, x_218);
lean_ctor_set(x_222, 1, x_219);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
x_223 = l_Lean_Xml_Parser_TokenizedType___closed__4;
lean_inc(x_1);
x_224 = l_Lean_Parsec_pstring(x_223, x_1);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_1);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = lean_box(0);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_229 = lean_ctor_get(x_224, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_224, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_231 = x_224;
} else {
 lean_dec_ref(x_224);
 x_231 = lean_box(0);
}
x_232 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_229);
if (x_232 == 0)
{
lean_object* x_233; 
lean_dec(x_1);
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_229);
lean_ctor_set(x_233, 1, x_230);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
x_234 = l_Lean_Xml_Parser_TokenizedType___closed__5;
lean_inc(x_1);
x_235 = l_Lean_Parsec_pstring(x_234, x_1);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_1);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
x_238 = lean_box(0);
if (lean_is_scalar(x_237)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_237;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_240 = lean_ctor_get(x_235, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_235, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_242 = x_235;
} else {
 lean_dec_ref(x_235);
 x_242 = lean_box(0);
}
x_243 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_240);
if (x_243 == 0)
{
lean_object* x_244; 
lean_dec(x_1);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_240);
lean_ctor_set(x_244, 1, x_241);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
x_245 = l_Lean_Xml_Parser_TokenizedType___closed__6;
lean_inc(x_1);
x_246 = l_Lean_Parsec_pstring(x_245, x_1);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_1);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
x_249 = lean_box(0);
if (lean_is_scalar(x_248)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_248;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_246, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_246, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_253 = x_246;
} else {
 lean_dec_ref(x_246);
 x_253 = lean_box(0);
}
x_254 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_251);
if (x_254 == 0)
{
lean_object* x_255; 
lean_dec(x_1);
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_251);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
x_256 = l_Lean_Xml_Parser_TokenizedType___closed__7;
x_257 = l_Lean_Parsec_pstring(x_256, x_1);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
x_260 = lean_box(0);
if (lean_is_scalar(x_259)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_259;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_257, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_257, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_264 = x_257;
} else {
 lean_dec_ref(x_257);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_266 = lean_ctor_get(x_3, 0);
x_267 = lean_ctor_get(x_3, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_3);
x_268 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_266);
if (x_268 == 0)
{
lean_object* x_269; 
lean_dec(x_1);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_267);
lean_dec(x_266);
x_270 = l_Lean_Xml_Parser_TokenizedType___closed__2;
lean_inc(x_1);
x_271 = l_Lean_Parsec_pstring(x_270, x_1);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_1);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
x_274 = lean_box(0);
if (lean_is_scalar(x_273)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_273;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_276 = lean_ctor_get(x_271, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_271, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_278 = x_271;
} else {
 lean_dec_ref(x_271);
 x_278 = lean_box(0);
}
x_279 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_276);
if (x_279 == 0)
{
lean_object* x_280; 
lean_dec(x_1);
if (lean_is_scalar(x_278)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_278;
}
lean_ctor_set(x_280, 0, x_276);
lean_ctor_set(x_280, 1, x_277);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
x_281 = l_Lean_Xml_Parser_TokenizedType___closed__3;
lean_inc(x_1);
x_282 = l_Lean_Parsec_pstring(x_281, x_1);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_1);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_284 = x_282;
} else {
 lean_dec_ref(x_282);
 x_284 = lean_box(0);
}
x_285 = lean_box(0);
if (lean_is_scalar(x_284)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_284;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_287 = lean_ctor_get(x_282, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_282, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_289 = x_282;
} else {
 lean_dec_ref(x_282);
 x_289 = lean_box(0);
}
x_290 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_287);
if (x_290 == 0)
{
lean_object* x_291; 
lean_dec(x_1);
if (lean_is_scalar(x_289)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_289;
}
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_288);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
x_292 = l_Lean_Xml_Parser_TokenizedType___closed__4;
lean_inc(x_1);
x_293 = l_Lean_Parsec_pstring(x_292, x_1);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_1);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_295 = x_293;
} else {
 lean_dec_ref(x_293);
 x_295 = lean_box(0);
}
x_296 = lean_box(0);
if (lean_is_scalar(x_295)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_295;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_298 = lean_ctor_get(x_293, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_293, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_300 = x_293;
} else {
 lean_dec_ref(x_293);
 x_300 = lean_box(0);
}
x_301 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_298);
if (x_301 == 0)
{
lean_object* x_302; 
lean_dec(x_1);
if (lean_is_scalar(x_300)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_300;
}
lean_ctor_set(x_302, 0, x_298);
lean_ctor_set(x_302, 1, x_299);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_298);
x_303 = l_Lean_Xml_Parser_TokenizedType___closed__5;
lean_inc(x_1);
x_304 = l_Lean_Parsec_pstring(x_303, x_1);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_1);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_306 = x_304;
} else {
 lean_dec_ref(x_304);
 x_306 = lean_box(0);
}
x_307 = lean_box(0);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_309 = lean_ctor_get(x_304, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_304, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_311 = x_304;
} else {
 lean_dec_ref(x_304);
 x_311 = lean_box(0);
}
x_312 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_309);
if (x_312 == 0)
{
lean_object* x_313; 
lean_dec(x_1);
if (lean_is_scalar(x_311)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_311;
}
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_310);
return x_313;
}
else
{
lean_object* x_314; lean_object* x_315; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
x_314 = l_Lean_Xml_Parser_TokenizedType___closed__6;
lean_inc(x_1);
x_315 = l_Lean_Parsec_pstring(x_314, x_1);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_1);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
x_318 = lean_box(0);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_320 = lean_ctor_get(x_315, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_315, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_322 = x_315;
} else {
 lean_dec_ref(x_315);
 x_322 = lean_box(0);
}
x_323 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_320);
if (x_323 == 0)
{
lean_object* x_324; 
lean_dec(x_1);
if (lean_is_scalar(x_322)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_322;
}
lean_ctor_set(x_324, 0, x_320);
lean_ctor_set(x_324, 1, x_321);
return x_324;
}
else
{
lean_object* x_325; lean_object* x_326; 
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
x_325 = l_Lean_Xml_Parser_TokenizedType___closed__7;
x_326 = l_Lean_Parsec_pstring(x_325, x_1);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_328 = x_326;
} else {
 lean_dec_ref(x_326);
 x_328 = lean_box(0);
}
x_329 = lean_box(0);
if (lean_is_scalar(x_328)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_328;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_331 = lean_ctor_get(x_326, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_326, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_333 = x_326;
} else {
 lean_dec_ref(x_326);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_NotationType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("NOTATION");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NotationType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Xml_Parser_NotationType___closed__1;
x_42 = l_Lean_Parsec_pstring(x_41, x_1);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Xml_Parser_S(x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint32_t x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_dec(x_47);
x_48 = 40;
x_49 = l_String_Iterator_hasNext(x_46);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 1, x_50);
return x_44;
}
else
{
lean_object* x_51; uint32_t x_52; uint8_t x_53; 
lean_inc(x_46);
x_51 = l_String_Iterator_next(x_46);
x_52 = l_String_Iterator_curr(x_46);
x_53 = x_52 == x_48;
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_51);
x_54 = l_Lean_Xml_Parser_Mixed___closed__7;
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 1, x_54);
return x_44;
}
else
{
lean_object* x_55; 
lean_free_object(x_44);
lean_dec(x_46);
lean_inc(x_51);
x_55 = l_Lean_Xml_Parser_S(x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_dec(x_51);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_15 = x_56;
goto block_40;
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 1);
x_60 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_51, x_58);
if (x_60 == 0)
{
lean_dec(x_51);
return x_55;
}
else
{
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
x_15 = x_51;
goto block_40;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_51, x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_51);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_dec(x_62);
lean_dec(x_61);
x_15 = x_51;
goto block_40;
}
}
}
}
}
}
else
{
lean_object* x_65; uint32_t x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
lean_dec(x_44);
x_66 = 40;
x_67 = l_String_Iterator_hasNext(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_Parsec_unexpectedEndOfInput;
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
else
{
lean_object* x_70; uint32_t x_71; uint8_t x_72; 
lean_inc(x_65);
x_70 = l_String_Iterator_next(x_65);
x_71 = l_String_Iterator_curr(x_65);
x_72 = x_71 == x_66;
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
x_73 = l_Lean_Xml_Parser_Mixed___closed__7;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_65);
lean_inc(x_70);
x_75 = l_Lean_Xml_Parser_S(x_70);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_dec(x_70);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_15 = x_76;
goto block_40;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_79 = x_75;
} else {
 lean_dec_ref(x_75);
 x_79 = lean_box(0);
}
x_80 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_70, x_77);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_70);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
x_15 = x_70;
goto block_40;
}
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_44);
if (x_82 == 0)
{
return x_44;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_44, 0);
x_84 = lean_ctor_get(x_44, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_44);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_42);
if (x_86 == 0)
{
return x_42;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_42, 0);
x_88 = lean_ctor_get(x_42, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_42);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 41;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_Mixed___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
block_40:
{
lean_object* x_16; 
x_16 = l_Lean_Xml_Parser_Name(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Xml_Parser_Mixed___closed__8;
x_19 = l_Lean_Parsec_many(lean_box(0));
x_20 = lean_apply_2(x_19, x_18, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_21);
x_22 = l_Lean_Xml_Parser_S(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_2 = x_23;
goto block_14;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_21, x_25);
if (x_27 == 0)
{
lean_dec(x_21);
return x_22;
}
else
{
lean_free_object(x_22);
lean_dec(x_26);
lean_dec(x_25);
x_2 = x_21;
goto block_14;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_21, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
x_2 = x_21;
goto block_14;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Nmtoken(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_Name___closed__1;
x_3 = l_Lean_Parsec_many1Chars(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Enumeration___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_26; 
lean_inc(x_1);
x_26 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_2 = x_27;
goto block_25;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_29);
if (x_31 == 0)
{
lean_dec(x_1);
return x_26;
}
else
{
lean_free_object(x_26);
lean_dec(x_30);
lean_dec(x_29);
x_2 = x_1;
goto block_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_dec(x_33);
lean_dec(x_32);
x_2 = x_1;
goto block_25;
}
}
}
block_25:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 124;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_Mixed___lambda__1___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
lean_inc(x_7);
x_12 = l_Lean_Xml_Parser_S(x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Xml_Parser_Nmtoken(x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_7, x_16);
if (x_18 == 0)
{
lean_dec(x_7);
return x_12;
}
else
{
lean_object* x_19; 
lean_free_object(x_12);
lean_dec(x_17);
lean_dec(x_16);
x_19 = l_Lean_Xml_Parser_Nmtoken(x_7);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_7, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
x_24 = l_Lean_Xml_Parser_Nmtoken(x_7);
return x_24;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_Enumeration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_Enumeration___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Enumeration(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; uint32_t x_41; uint8_t x_42; 
x_41 = 40;
x_42 = l_String_Iterator_hasNext(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Parsec_unexpectedEndOfInput;
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
lean_inc(x_1);
x_45 = l_String_Iterator_next(x_1);
x_46 = l_String_Iterator_curr(x_1);
x_47 = x_46 == x_41;
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
x_48 = l_Lean_Xml_Parser_Mixed___closed__7;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_1);
lean_inc(x_45);
x_50 = l_Lean_Xml_Parser_S(x_45);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec(x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_15 = x_51;
goto block_40;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_ctor_get(x_50, 1);
x_55 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_45, x_53);
if (x_55 == 0)
{
lean_dec(x_45);
return x_50;
}
else
{
lean_free_object(x_50);
lean_dec(x_54);
lean_dec(x_53);
x_15 = x_45;
goto block_40;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_45, x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_45);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
x_15 = x_45;
goto block_40;
}
}
}
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 41;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_Mixed___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
block_40:
{
lean_object* x_16; 
x_16 = l_Lean_Xml_Parser_Nmtoken(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Xml_Parser_Enumeration___closed__1;
x_19 = l_Lean_Parsec_many(lean_box(0));
x_20 = lean_apply_2(x_19, x_18, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_21);
x_22 = l_Lean_Xml_Parser_S(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_2 = x_23;
goto block_14;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_21, x_25);
if (x_27 == 0)
{
lean_dec(x_21);
return x_22;
}
else
{
lean_free_object(x_22);
lean_dec(x_26);
lean_dec(x_25);
x_2 = x_21;
goto block_14;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_21, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
x_2 = x_21;
goto block_14;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EnumeratedType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_NotationType(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_8);
if (x_10 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Xml_Parser_Enumeration(x_1);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
x_16 = l_Lean_Xml_Parser_Enumeration(x_1);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_StringType(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_8);
if (x_10 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Xml_Parser_TokenizedType(x_1);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
x_19 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_17);
if (x_19 == 0)
{
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_20; 
lean_free_object(x_11);
lean_dec(x_18);
lean_dec(x_17);
x_20 = l_Lean_Xml_Parser_EnumeratedType(x_1);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_21);
x_25 = l_Lean_Xml_Parser_EnumeratedType(x_1);
return x_25;
}
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_28 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_26);
lean_inc(x_1);
x_30 = l_Lean_Xml_Parser_TokenizedType(x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
x_38 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_35);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_1);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
x_40 = l_Lean_Xml_Parser_EnumeratedType(x_1);
return x_40;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lt");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("gt");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("amp");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("apos");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quot");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__6___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__6___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__7___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 39;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__7___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__8___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 38;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__8___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__9___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 62;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__9___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__10___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 60;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__10___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_predefinedEntityToChar(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__2;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__3;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__4;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__5;
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__6;
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__7;
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__8;
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__9;
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Xml_Parser_predefinedEntityToChar___closed__10;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_predefinedEntityToChar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_predefinedEntityToChar(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EntityRef___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 38;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EntityRef___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_EntityRef___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EntityRef___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_EntityRef___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EntityRef___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 59;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EntityRef___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_EntityRef___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EntityRef___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_EntityRef___closed__5;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityRef(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 38;
x_3 = l_String_Iterator_hasNext(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parsec_unexpectedEndOfInput;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
lean_inc(x_1);
x_6 = l_String_Iterator_next(x_1);
x_7 = l_String_Iterator_curr(x_1);
x_8 = x_7 == x_2;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = l_Lean_Xml_Parser_EntityRef___closed__3;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Xml_Parser_Name(x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Xml_Parser_predefinedEntityToChar(x_14);
lean_dec(x_14);
x_16 = 59;
x_17 = l_String_Iterator_hasNext(x_13);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_13);
x_18 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
lean_inc(x_13);
x_19 = l_String_Iterator_next(x_13);
x_20 = l_String_Iterator_curr(x_13);
lean_dec(x_13);
x_21 = x_20 == x_16;
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_15);
x_22 = l_Lean_Xml_Parser_EntityRef___closed__6;
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_22);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_11, 1, x_15);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = l_Lean_Xml_Parser_predefinedEntityToChar(x_24);
lean_dec(x_24);
x_26 = 59;
x_27 = l_String_Iterator_hasNext(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_23);
x_28 = l_Lean_Parsec_unexpectedEndOfInput;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
lean_inc(x_23);
x_30 = l_String_Iterator_next(x_23);
x_31 = l_String_Iterator_curr(x_23);
lean_dec(x_23);
x_32 = x_31 == x_26;
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_25);
x_33 = l_Lean_Xml_Parser_EntityRef___closed__6;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_25);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_11, 0);
lean_dec(x_37);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_dec(x_11);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_hexDigitToNat(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_23; uint8_t x_24; 
x_23 = 48;
x_24 = x_23 <= x_1;
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_box(0);
x_2 = x_25;
goto block_22;
}
else
{
uint32_t x_26; uint8_t x_27; 
x_26 = 57;
x_27 = x_1 <= x_26;
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
x_2 = x_28;
goto block_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_uint32_to_nat(x_1);
x_30 = lean_unsigned_to_nat(48u);
x_31 = lean_nat_sub(x_29, x_30);
lean_dec(x_29);
return x_31;
}
}
block_22:
{
uint32_t x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = 97;
x_4 = x_3 <= x_1;
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_uint32_to_nat(x_1);
x_6 = lean_unsigned_to_nat(65u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(10u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
return x_9;
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 102;
x_11 = x_1 <= x_10;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_uint32_to_nat(x_1);
x_13 = lean_unsigned_to_nat(65u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(10u);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_uint32_to_nat(x_1);
x_18 = lean_unsigned_to_nat(97u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(10u);
x_21 = lean_nat_add(x_19, x_20);
lean_dec(x_19);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_hexDigitToNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Xml_Parser_hexDigitToNat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_digitsToNat___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_nat_mul(x_5, x_1);
lean_dec(x_5);
x_9 = lean_nat_add(x_8, x_7);
lean_dec(x_7);
lean_dec(x_8);
x_10 = 1;
x_11 = x_3 + x_10;
x_3 = x_11;
x_5 = x_9;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_digitsToNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_digitsToNat___spec__1(x_1, x_2, x_9, x_10, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_digitsToNat___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_digitsToNat___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_digitsToNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Xml_Parser_digitsToNat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CharRef___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Parsec_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
lean_inc(x_1);
x_5 = l_String_Iterator_next(x_1);
x_6 = l_String_Iterator_curr(x_1);
x_7 = 48;
x_8 = x_7 <= x_6;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = l_Lean_Xml_Parser_NameChar___closed__11;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 57;
x_12 = x_6 <= x_11;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = l_Lean_Xml_Parser_NameChar___closed__11;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_15 = lean_uint32_to_nat(x_6);
x_16 = lean_unsigned_to_nat(48u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_CharRef___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hex digit expected");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CharRef___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_39; 
x_39 = l_String_Iterator_hasNext(x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_Parsec_unexpectedEndOfInput;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; uint32_t x_43; lean_object* x_44; uint32_t x_63; uint8_t x_64; 
lean_inc(x_1);
x_42 = l_String_Iterator_next(x_1);
x_43 = l_String_Iterator_curr(x_1);
x_63 = 48;
x_64 = x_63 <= x_43;
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_box(0);
x_44 = x_65;
goto block_62;
}
else
{
uint32_t x_66; uint8_t x_67; 
x_66 = 57;
x_67 = x_43 <= x_66;
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_box(0);
x_44 = x_68;
goto block_62;
}
else
{
lean_dec(x_1);
x_2 = x_42;
x_3 = x_43;
goto block_38;
}
}
block_62:
{
uint32_t x_45; uint8_t x_46; 
lean_dec(x_44);
x_45 = 97;
x_46 = x_45 <= x_43;
if (x_46 == 0)
{
uint32_t x_47; uint8_t x_48; 
x_47 = 65;
x_48 = x_47 <= x_43;
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_42);
x_49 = l_Lean_Xml_Parser_CharRef___lambda__2___closed__1;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = x_43 <= x_47;
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_42);
x_52 = l_Lean_Xml_Parser_CharRef___lambda__2___closed__1;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
else
{
lean_dec(x_1);
x_2 = x_42;
x_3 = x_43;
goto block_38;
}
}
}
else
{
uint8_t x_54; 
x_54 = x_43 <= x_45;
if (x_54 == 0)
{
uint32_t x_55; uint8_t x_56; 
x_55 = 65;
x_56 = x_55 <= x_43;
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_42);
x_57 = l_Lean_Xml_Parser_CharRef___lambda__2___closed__1;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
else
{
uint8_t x_59; 
x_59 = x_43 <= x_55;
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_42);
x_60 = l_Lean_Xml_Parser_CharRef___lambda__2___closed__1;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
else
{
lean_dec(x_1);
x_2 = x_42;
x_3 = x_43;
goto block_38;
}
}
}
else
{
lean_dec(x_1);
x_2 = x_42;
x_3 = x_43;
goto block_38;
}
}
}
}
block_38:
{
lean_object* x_4; uint32_t x_28; uint8_t x_29; 
x_28 = 48;
x_29 = x_28 <= x_3;
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_4 = x_30;
goto block_27;
}
else
{
uint32_t x_31; uint8_t x_32; 
x_31 = 57;
x_32 = x_3 <= x_31;
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_4 = x_33;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_uint32_to_nat(x_3);
x_35 = lean_unsigned_to_nat(48u);
x_36 = lean_nat_sub(x_34, x_35);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
block_27:
{
uint32_t x_5; uint8_t x_6; 
lean_dec(x_4);
x_5 = 97;
x_6 = x_5 <= x_3;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_uint32_to_nat(x_3);
x_8 = lean_unsigned_to_nat(65u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(10u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 102;
x_14 = x_3 <= x_13;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_uint32_to_nat(x_3);
x_16 = lean_unsigned_to_nat(65u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(10u);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_uint32_to_nat(x_3);
x_22 = lean_unsigned_to_nat(97u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(10u);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_CharRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("&#");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_CharRef___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_CharRef___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_CharRef___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_CharRef___lambda__2), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CharRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Xml_Parser_CharRef___closed__1;
x_19 = l_Lean_Parsec_pstring(x_18, x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Xml_Parser_CharRef___closed__2;
x_22 = l_Lean_Parsec_many1(lean_box(0));
lean_inc(x_20);
x_23 = lean_apply_2(x_22, x_21, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(10u);
x_27 = l_Lean_Xml_Parser_digitsToNat(x_26, x_25);
lean_dec(x_25);
x_2 = x_24;
x_3 = x_27;
goto block_17;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
x_31 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_20, x_29);
if (x_31 == 0)
{
lean_dec(x_20);
return x_23;
}
else
{
uint32_t x_32; uint8_t x_33; 
lean_dec(x_30);
lean_dec(x_29);
x_32 = 120;
x_33 = l_String_Iterator_hasNext(x_20);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set(x_23, 1, x_34);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_35; uint32_t x_36; uint8_t x_37; 
lean_inc(x_20);
x_35 = l_String_Iterator_next(x_20);
x_36 = l_String_Iterator_curr(x_20);
x_37 = x_36 == x_32;
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
x_38 = l_Lean_Xml_Parser_PITarget___closed__15;
lean_ctor_set(x_23, 1, x_38);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_23);
lean_dec(x_20);
x_39 = l_Lean_Xml_Parser_CharRef___closed__3;
x_40 = l_Lean_Parsec_many1(lean_box(0));
x_41 = lean_apply_2(x_40, x_39, x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(16u);
x_45 = l_Lean_Xml_Parser_digitsToNat(x_44, x_43);
lean_dec(x_43);
x_2 = x_42;
x_3 = x_45;
goto block_17;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_23, 0);
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_23);
x_52 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_20, x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_20);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
uint32_t x_54; uint8_t x_55; 
lean_dec(x_51);
lean_dec(x_50);
x_54 = 120;
x_55 = l_String_Iterator_hasNext(x_20);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_Parsec_unexpectedEndOfInput;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_20);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_object* x_58; uint32_t x_59; uint8_t x_60; 
lean_inc(x_20);
x_58 = l_String_Iterator_next(x_20);
x_59 = l_String_Iterator_curr(x_20);
x_60 = x_59 == x_54;
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
x_61 = l_Lean_Xml_Parser_PITarget___closed__15;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_20);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_20);
x_63 = l_Lean_Xml_Parser_CharRef___closed__3;
x_64 = l_Lean_Parsec_many1(lean_box(0));
x_65 = lean_apply_2(x_64, x_63, x_58);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unsigned_to_nat(16u);
x_69 = l_Lean_Xml_Parser_digitsToNat(x_68, x_67);
lean_dec(x_67);
x_2 = x_66;
x_3 = x_69;
goto block_17;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
}
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_19);
if (x_74 == 0)
{
return x_19;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_19, 0);
x_76 = lean_ctor_get(x_19, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_19);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
block_17:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 59;
x_5 = l_String_Iterator_hasNext(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = l_Lean_Parsec_unexpectedEndOfInput;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; 
lean_inc(x_2);
x_8 = l_String_Iterator_next(x_2);
x_9 = l_String_Iterator_curr(x_2);
x_10 = x_9 == x_4;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
x_11 = l_Lean_Xml_Parser_EntityRef___closed__6;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_13 = l_Char_ofNat(x_3);
lean_dec(x_3);
x_14 = lean_unbox_uint32(x_13);
lean_dec(x_13);
x_15 = lean_box_uint32(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Reference(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_EntityRef(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_8);
if (x_10 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Xml_Parser_CharRef(x_1);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_11, 1, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_25 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
x_27 = l_Lean_Xml_Parser_CharRef(x_1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_AttValue___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = x_2 + x_7;
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; uint32_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_unbox_uint32(x_10);
lean_dec(x_10);
x_12 = lean_string_push(x_4, x_11);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttValue___lambda__1(uint32_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Iterator_hasNext(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Lean_Xml_Parser_Reference(x_2);
return x_7;
}
}
else
{
lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; uint8_t x_12; 
lean_inc(x_2);
x_8 = l_String_Iterator_next(x_2);
x_9 = l_String_Iterator_curr(x_2);
x_10 = 60;
x_11 = x_9 == x_10;
x_12 = l_instDecidableNot___rarg(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Xml_Parser_NameChar___closed__1;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Xml_Parser_Reference(x_2);
return x_16;
}
}
else
{
uint32_t x_17; uint8_t x_18; uint8_t x_19; 
x_17 = 38;
x_18 = x_9 == x_17;
x_19 = l_instDecidableNot___rarg(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_8);
x_20 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Xml_Parser_NameChar___closed__1;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_Xml_Parser_Reference(x_2);
return x_23;
}
}
else
{
uint8_t x_24; uint8_t x_25; 
x_24 = x_9 == x_1;
x_25 = l_instDecidableNot___rarg(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_8);
x_26 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Xml_Parser_NameChar___closed__1;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Xml_Parser_Reference(x_2);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = lean_box_uint32(x_9);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_AttValue___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 39;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_AttValue___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_AttValue___closed__1___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_AttValue___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_AttValue___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_AttValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_AttValue___closed__2___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_AttValue___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttValue(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_18; lean_object* x_19; uint32_t x_58; uint8_t x_59; 
x_58 = 34;
x_59 = l_String_Iterator_hasNext(x_1);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_18 = x_1;
x_19 = x_60;
goto block_57;
}
else
{
lean_object* x_61; uint32_t x_62; uint8_t x_63; 
lean_inc(x_1);
x_61 = l_String_Iterator_next(x_1);
x_62 = l_String_Iterator_curr(x_1);
x_63 = x_62 == x_58;
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
x_64 = l_Lean_Xml_Parser_quote___rarg___closed__3;
lean_inc(x_1);
x_18 = x_1;
x_19 = x_64;
goto block_57;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = l_Lean_Xml_Parser_AttValue___closed__2;
x_66 = l_Lean_Parsec_many(lean_box(0));
x_67 = lean_apply_2(x_66, x_65, x_61);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_String_Iterator_hasNext(x_68);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_69);
x_71 = l_Lean_Parsec_unexpectedEndOfInput;
x_18 = x_68;
x_19 = x_71;
goto block_57;
}
else
{
lean_object* x_72; uint32_t x_73; uint8_t x_74; 
lean_inc(x_68);
x_72 = l_String_Iterator_next(x_68);
x_73 = l_String_Iterator_curr(x_68);
x_74 = x_73 == x_58;
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_72);
lean_dec(x_69);
x_75 = l_Lean_Xml_Parser_quote___rarg___closed__3;
x_18 = x_68;
x_19 = x_75;
goto block_57;
}
else
{
lean_dec(x_68);
lean_dec(x_1);
x_2 = x_72;
x_3 = x_69;
goto block_17;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_dec(x_67);
x_18 = x_76;
x_19 = x_77;
goto block_57;
}
}
}
block_17:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = l_Lean_Xml_Parser_endl___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = l_Lean_Xml_Parser_endl___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = l_Lean_Xml_Parser_endl___closed__1;
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_AttValue___spec__1(x_3, x_12, x_13, x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
block_57:
{
uint8_t x_20; 
x_20 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
uint32_t x_22; uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_18);
x_22 = 39;
x_23 = l_String_Iterator_hasNext(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Parsec_unexpectedEndOfInput;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint32_t x_27; uint8_t x_28; 
lean_inc(x_1);
x_26 = l_String_Iterator_next(x_1);
x_27 = l_String_Iterator_curr(x_1);
x_28 = x_27 == x_22;
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
x_29 = l_Lean_Xml_Parser_quote___rarg___closed__6;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_31 = l_Lean_Xml_Parser_AttValue___closed__1;
x_32 = l_Lean_Parsec_many(lean_box(0));
x_33 = lean_apply_2(x_32, x_31, x_26);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = l_String_Iterator_hasNext(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_38);
return x_33;
}
else
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; 
lean_inc(x_35);
x_39 = l_String_Iterator_next(x_35);
x_40 = l_String_Iterator_curr(x_35);
x_41 = x_40 == x_22;
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_36);
x_42 = l_Lean_Xml_Parser_quote___rarg___closed__6;
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_42);
return x_33;
}
else
{
lean_free_object(x_33);
lean_dec(x_35);
x_2 = x_39;
x_3 = x_36;
goto block_17;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = l_String_Iterator_hasNext(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_44);
x_46 = l_Lean_Parsec_unexpectedEndOfInput;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; 
lean_inc(x_43);
x_48 = l_String_Iterator_next(x_43);
x_49 = l_String_Iterator_curr(x_43);
x_50 = x_49 == x_22;
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_48);
lean_dec(x_44);
x_51 = l_Lean_Xml_Parser_quote___rarg___closed__6;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
else
{
lean_dec(x_43);
x_2 = x_48;
x_3 = x_44;
goto block_17;
}
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_33);
if (x_53 == 0)
{
return x_33;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_33, 0);
x_55 = lean_ctor_get(x_33, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_33);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_AttValue___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_AttValue___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttValue___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Xml_Parser_AttValue___lambda__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Xml_Parser_DefaultDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#REQUIRED");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_DefaultDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#IMPLIED");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_DefaultDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#FIXED");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_DefaultDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_DefaultDecl___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_11);
if (x_13 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_3);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_Lean_Xml_Parser_DefaultDecl___closed__2;
lean_inc(x_1);
x_15 = l_Lean_Parsec_pstring(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 1, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_23);
if (x_25 == 0)
{
lean_dec(x_1);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
lean_dec(x_24);
lean_dec(x_23);
x_26 = l_Lean_Xml_Parser_DefaultDecl___closed__3;
lean_inc(x_1);
x_27 = l_Lean_Parsec_pstring(x_26, x_1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Xml_Parser_S(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Xml_Parser_AttValue(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 1);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 1, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
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
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
x_45 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_43);
if (x_45 == 0)
{
lean_dec(x_1);
return x_29;
}
else
{
lean_object* x_46; 
lean_free_object(x_29);
lean_dec(x_44);
lean_dec(x_43);
x_46 = l_Lean_Xml_Parser_AttValue(x_1);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 1);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 1, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_29, 0);
x_58 = lean_ctor_get(x_29, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_29);
x_59 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_57);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_1);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; 
lean_dec(x_58);
lean_dec(x_57);
x_61 = l_Lean_Xml_Parser_AttValue(x_1);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_27);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_27, 0);
x_72 = lean_ctor_get(x_27, 1);
x_73 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_71);
if (x_73 == 0)
{
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_74; 
lean_free_object(x_27);
lean_dec(x_72);
lean_dec(x_71);
x_74 = l_Lean_Xml_Parser_AttValue(x_1);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 1);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_74, 1, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_74);
if (x_81 == 0)
{
return x_74;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_74, 0);
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_74);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_27, 0);
x_86 = lean_ctor_get(x_27, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_27);
x_87 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_85);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_1);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_85);
x_89 = l_Lean_Xml_Parser_AttValue(x_1);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 0);
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
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_15, 0);
x_99 = lean_ctor_get(x_15, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_15);
x_100 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_98);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_1);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_99);
lean_dec(x_98);
x_102 = l_Lean_Xml_Parser_DefaultDecl___closed__3;
lean_inc(x_1);
x_103 = l_Lean_Parsec_pstring(x_102, x_1);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l_Lean_Xml_Parser_S(x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_1);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec(x_105);
x_107 = l_Lean_Xml_Parser_AttValue(x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_105, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_118 = x_105;
} else {
 lean_dec_ref(x_105);
 x_118 = lean_box(0);
}
x_119 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_116);
if (x_119 == 0)
{
lean_object* x_120; 
lean_dec(x_1);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
else
{
lean_object* x_121; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
x_121 = l_Lean_Xml_Parser_AttValue(x_1);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_121, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_121, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_128 = x_121;
} else {
 lean_dec_ref(x_121);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_103, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_103, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_132 = x_103;
} else {
 lean_dec_ref(x_103);
 x_132 = lean_box(0);
}
x_133 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_130);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_1);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
else
{
lean_object* x_135; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
x_135 = l_Lean_Xml_Parser_AttValue(x_1);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
x_138 = lean_box(0);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_142 = x_135;
} else {
 lean_dec_ref(x_135);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
}
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = lean_ctor_get(x_3, 0);
x_145 = lean_ctor_get(x_3, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_3);
x_146 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_144);
if (x_146 == 0)
{
lean_object* x_147; 
lean_dec(x_1);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_145);
lean_dec(x_144);
x_148 = l_Lean_Xml_Parser_DefaultDecl___closed__2;
lean_inc(x_1);
x_149 = l_Lean_Parsec_pstring(x_148, x_1);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_1);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = lean_box(0);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_154 = lean_ctor_get(x_149, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_156 = x_149;
} else {
 lean_dec_ref(x_149);
 x_156 = lean_box(0);
}
x_157 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_154);
if (x_157 == 0)
{
lean_object* x_158; 
lean_dec(x_1);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
x_159 = l_Lean_Xml_Parser_DefaultDecl___closed__3;
lean_inc(x_1);
x_160 = l_Lean_Parsec_pstring(x_159, x_1);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Lean_Xml_Parser_S(x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_1);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_Lean_Xml_Parser_AttValue(x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
x_167 = lean_box(0);
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_166;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_164, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_171 = x_164;
} else {
 lean_dec_ref(x_164);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_173 = lean_ctor_get(x_162, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_162, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_175 = x_162;
} else {
 lean_dec_ref(x_162);
 x_175 = lean_box(0);
}
x_176 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_173);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_1);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
return x_177;
}
else
{
lean_object* x_178; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
x_178 = l_Lean_Xml_Parser_AttValue(x_1);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
x_181 = lean_box(0);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_178, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_178, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_185 = x_178;
} else {
 lean_dec_ref(x_178);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_160, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_160, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_189 = x_160;
} else {
 lean_dec_ref(x_160);
 x_189 = lean_box(0);
}
x_190 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_187);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_1);
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_189;
}
lean_ctor_set(x_191, 0, x_187);
lean_ctor_set(x_191, 1, x_188);
return x_191;
}
else
{
lean_object* x_192; 
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
x_192 = l_Lean_Xml_Parser_AttValue(x_1);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
x_195 = lean_box(0);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_199 = x_192;
} else {
 lean_dec_ref(x_192);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttDef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Xml_Parser_Name(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Xml_Parser_S(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Xml_Parser_AttType(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Xml_Parser_S(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Xml_Parser_DefaultDecl(x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
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
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
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
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
return x_2;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_AttlistDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<!ATTLIST");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_AttlistDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_AttDef), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_AttlistDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Xml_Parser_AttlistDecl___closed__1;
x_16 = l_Lean_Parsec_pstring(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Xml_Parser_S(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Xml_Parser_Name(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Xml_Parser_AttlistDecl___closed__2;
x_23 = l_Lean_Parsec_many(lean_box(0));
x_24 = lean_apply_2(x_23, x_22, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_25);
x_26 = l_Lean_Xml_Parser_S(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_2 = x_27;
goto block_14;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_25, x_29);
if (x_31 == 0)
{
lean_dec(x_25);
return x_26;
}
else
{
lean_free_object(x_26);
lean_dec(x_30);
lean_dec(x_29);
x_2 = x_25;
goto block_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_25, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_dec(x_33);
lean_dec(x_32);
x_2 = x_25;
goto block_14;
}
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_18);
if (x_44 == 0)
{
return x_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
return x_16;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_16, 0);
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_16);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 62;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_elementDecl___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_PEReference___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 37;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PEReference___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_PEReference___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_PEReference___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_PEReference___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PEReference(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 37;
x_3 = l_String_Iterator_hasNext(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parsec_unexpectedEndOfInput;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
lean_inc(x_1);
x_6 = l_String_Iterator_next(x_1);
x_7 = l_String_Iterator_curr(x_1);
x_8 = x_7 == x_2;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = l_Lean_Xml_Parser_PEReference___closed__3;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Xml_Parser_Name(x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
x_15 = 59;
x_16 = l_String_Iterator_hasNext(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_17);
return x_11;
}
else
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
lean_inc(x_13);
x_18 = l_String_Iterator_next(x_13);
x_19 = l_String_Iterator_curr(x_13);
x_20 = x_19 == x_15;
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
x_21 = l_Lean_Xml_Parser_EntityRef___closed__6;
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 1, x_21);
return x_11;
}
else
{
lean_object* x_22; 
lean_dec(x_13);
x_22 = lean_box(0);
lean_ctor_set(x_11, 1, x_22);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
}
}
else
{
lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = 59;
x_25 = l_String_Iterator_hasNext(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Parsec_unexpectedEndOfInput;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; uint32_t x_29; uint8_t x_30; 
lean_inc(x_23);
x_28 = l_String_Iterator_next(x_23);
x_29 = l_String_Iterator_curr(x_23);
x_30 = x_29 == x_24;
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
x_31 = l_Lean_Xml_Parser_EntityRef___closed__6;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
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
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityValue___lambda__1(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_25; 
x_25 = l_String_Iterator_hasNext(x_2);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_2);
x_3 = x_2;
x_4 = x_26;
goto block_24;
}
else
{
lean_object* x_27; uint32_t x_28; uint32_t x_29; uint8_t x_30; uint8_t x_31; 
lean_inc(x_2);
x_27 = l_String_Iterator_next(x_2);
x_28 = l_String_Iterator_curr(x_2);
x_29 = 37;
x_30 = x_28 == x_29;
x_31 = l_instDecidableNot___rarg(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
x_32 = l_Lean_Xml_Parser_NameChar___closed__1;
lean_inc(x_2);
x_3 = x_2;
x_4 = x_32;
goto block_24;
}
else
{
uint32_t x_33; uint8_t x_34; uint8_t x_35; 
x_33 = 38;
x_34 = x_28 == x_33;
x_35 = l_instDecidableNot___rarg(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_27);
x_36 = l_Lean_Xml_Parser_NameChar___closed__1;
lean_inc(x_2);
x_3 = x_2;
x_4 = x_36;
goto block_24;
}
else
{
uint8_t x_37; uint8_t x_38; 
x_37 = x_28 == x_1;
x_38 = l_instDecidableNot___rarg(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_27);
x_39 = l_Lean_Xml_Parser_NameChar___closed__1;
lean_inc(x_2);
x_3 = x_2;
x_4 = x_39;
goto block_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
x_40 = lean_box_uint32(x_28);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
block_24:
{
uint8_t x_5; 
x_5 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
x_7 = l_Lean_Xml_Parser_PEReference(x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_7, 1, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
x_17 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_15);
if (x_17 == 0)
{
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_18; 
lean_free_object(x_7);
lean_dec(x_16);
lean_dec(x_15);
x_18 = l_Lean_Xml_Parser_Reference(x_2);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
x_23 = l_Lean_Xml_Parser_Reference(x_2);
return x_23;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_EntityValue___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 39;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EntityValue___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_EntityValue___closed__1___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_EntityValue___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EntityValue___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EntityValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_EntityValue___closed__2___boxed__const__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_EntityValue___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityValue(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_18; lean_object* x_19; uint32_t x_58; uint8_t x_59; 
x_58 = 34;
x_59 = l_String_Iterator_hasNext(x_1);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_Lean_Parsec_unexpectedEndOfInput;
lean_inc(x_1);
x_18 = x_1;
x_19 = x_60;
goto block_57;
}
else
{
lean_object* x_61; uint32_t x_62; uint8_t x_63; 
lean_inc(x_1);
x_61 = l_String_Iterator_next(x_1);
x_62 = l_String_Iterator_curr(x_1);
x_63 = x_62 == x_58;
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
x_64 = l_Lean_Xml_Parser_quote___rarg___closed__3;
lean_inc(x_1);
x_18 = x_1;
x_19 = x_64;
goto block_57;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = l_Lean_Xml_Parser_EntityValue___closed__2;
x_66 = l_Lean_Parsec_many(lean_box(0));
x_67 = lean_apply_2(x_66, x_65, x_61);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_String_Iterator_hasNext(x_68);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_69);
x_71 = l_Lean_Parsec_unexpectedEndOfInput;
x_18 = x_68;
x_19 = x_71;
goto block_57;
}
else
{
lean_object* x_72; uint32_t x_73; uint8_t x_74; 
lean_inc(x_68);
x_72 = l_String_Iterator_next(x_68);
x_73 = l_String_Iterator_curr(x_68);
x_74 = x_73 == x_58;
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_72);
lean_dec(x_69);
x_75 = l_Lean_Xml_Parser_quote___rarg___closed__3;
x_18 = x_68;
x_19 = x_75;
goto block_57;
}
else
{
lean_dec(x_68);
lean_dec(x_1);
x_2 = x_72;
x_3 = x_69;
goto block_17;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_dec(x_67);
x_18 = x_76;
x_19 = x_77;
goto block_57;
}
}
}
block_17:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = l_Lean_Xml_Parser_endl___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = l_Lean_Xml_Parser_endl___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = l_Lean_Xml_Parser_endl___closed__1;
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_AttValue___spec__1(x_3, x_12, x_13, x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
block_57:
{
uint8_t x_20; 
x_20 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
uint32_t x_22; uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_18);
x_22 = 39;
x_23 = l_String_Iterator_hasNext(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Parsec_unexpectedEndOfInput;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint32_t x_27; uint8_t x_28; 
lean_inc(x_1);
x_26 = l_String_Iterator_next(x_1);
x_27 = l_String_Iterator_curr(x_1);
x_28 = x_27 == x_22;
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
x_29 = l_Lean_Xml_Parser_quote___rarg___closed__6;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_31 = l_Lean_Xml_Parser_EntityValue___closed__1;
x_32 = l_Lean_Parsec_many(lean_box(0));
x_33 = lean_apply_2(x_32, x_31, x_26);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = l_String_Iterator_hasNext(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_38);
return x_33;
}
else
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; 
lean_inc(x_35);
x_39 = l_String_Iterator_next(x_35);
x_40 = l_String_Iterator_curr(x_35);
x_41 = x_40 == x_22;
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_36);
x_42 = l_Lean_Xml_Parser_quote___rarg___closed__6;
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_42);
return x_33;
}
else
{
lean_free_object(x_33);
lean_dec(x_35);
x_2 = x_39;
x_3 = x_36;
goto block_17;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = l_String_Iterator_hasNext(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_44);
x_46 = l_Lean_Parsec_unexpectedEndOfInput;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
else
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; 
lean_inc(x_43);
x_48 = l_String_Iterator_next(x_43);
x_49 = l_String_Iterator_curr(x_43);
x_50 = x_49 == x_22;
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_48);
lean_dec(x_44);
x_51 = l_Lean_Xml_Parser_quote___rarg___closed__6;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
else
{
lean_dec(x_43);
x_2 = x_48;
x_3 = x_44;
goto block_17;
}
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_33);
if (x_53 == 0)
{
return x_33;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_33, 0);
x_55 = lean_ctor_get(x_33, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_33);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityValue___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Xml_Parser_EntityValue___lambda__1(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Xml_Parser_NDataDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("NDATA");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NDataDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Xml_Parser_NDataDecl___closed__1;
x_5 = l_Lean_Parsec_pstring(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Xml_Parser_S(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Xml_Parser_Name(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 1, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityDef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_EntityValue(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
x_5 = lean_box(0);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_10);
if (x_12 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_10);
x_13 = l_Lean_Xml_Parser_ExternalID(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Xml_Parser_NDataDecl(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 1);
lean_dec(x_18);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
x_24 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_14, x_22);
if (x_24 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
return x_16;
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_14, x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_15);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_15);
return x_29;
}
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_36 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_34);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_34);
x_38 = l_Lean_Xml_Parser_ExternalID(x_1);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_39);
x_41 = l_Lean_Xml_Parser_NDataDecl(x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_47 = x_41;
} else {
 lean_dec_ref(x_41);
 x_47 = lean_box(0);
}
x_48 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_39, x_45);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_40);
lean_dec(x_39);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_45);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
 lean_ctor_set_tag(x_50, 0);
}
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_40);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_GEDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<!ENTITY");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_GEDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Xml_Parser_GEDecl___closed__1;
x_16 = l_Lean_Parsec_pstring(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Xml_Parser_S(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Xml_Parser_Name(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Xml_Parser_S(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Xml_Parser_EntityDef(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_25);
x_26 = l_Lean_Xml_Parser_S(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_2 = x_27;
goto block_14;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
x_31 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_25, x_29);
if (x_31 == 0)
{
lean_dec(x_25);
return x_26;
}
else
{
lean_free_object(x_26);
lean_dec(x_30);
lean_dec(x_29);
x_2 = x_25;
goto block_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_25, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_dec(x_33);
lean_dec(x_32);
x_2 = x_25;
goto block_14;
}
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
return x_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_22, 0);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_18);
if (x_48 == 0)
{
return x_18;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_18);
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
x_52 = !lean_is_exclusive(x_16);
if (x_52 == 0)
{
return x_16;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_16, 0);
x_54 = lean_ctor_get(x_16, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_16);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 62;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_elementDecl___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PEDef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_EntityValue(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
x_5 = lean_box(0);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_10);
if (x_12 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_10);
x_13 = l_Lean_Xml_Parser_ExternalID(x_1);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = l_Lean_Xml_Parser_ExternalID(x_1);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PEDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Xml_Parser_GEDecl___closed__1;
x_16 = l_Lean_Parsec_pstring(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Xml_Parser_S(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_dec(x_21);
x_22 = 37;
x_23 = l_String_Iterator_hasNext(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 1, x_24);
return x_18;
}
else
{
lean_object* x_25; uint32_t x_26; uint8_t x_27; 
lean_inc(x_20);
x_25 = l_String_Iterator_next(x_20);
x_26 = l_String_Iterator_curr(x_20);
x_27 = x_26 == x_22;
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
x_28 = l_Lean_Xml_Parser_PEReference___closed__3;
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 1, x_28);
return x_18;
}
else
{
lean_object* x_29; 
lean_free_object(x_18);
lean_dec(x_20);
x_29 = l_Lean_Xml_Parser_S(x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Xml_Parser_Name(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Xml_Parser_PEDef(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_34);
x_35 = l_Lean_Xml_Parser_S(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_2 = x_36;
goto block_14;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
x_40 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_34, x_38);
if (x_40 == 0)
{
lean_dec(x_34);
return x_35;
}
else
{
lean_free_object(x_35);
lean_dec(x_39);
lean_dec(x_38);
x_2 = x_34;
goto block_14;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_43 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_34, x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_dec(x_42);
lean_dec(x_41);
x_2 = x_34;
goto block_14;
}
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
return x_31;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_31, 0);
x_51 = lean_ctor_get(x_31, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_31);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_29);
if (x_53 == 0)
{
return x_29;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_29, 0);
x_55 = lean_ctor_get(x_29, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_29);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
else
{
lean_object* x_57; uint32_t x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_18, 0);
lean_inc(x_57);
lean_dec(x_18);
x_58 = 37;
x_59 = l_String_Iterator_hasNext(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Parsec_unexpectedEndOfInput;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
else
{
lean_object* x_62; uint32_t x_63; uint8_t x_64; 
lean_inc(x_57);
x_62 = l_String_Iterator_next(x_57);
x_63 = l_String_Iterator_curr(x_57);
x_64 = x_63 == x_58;
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
x_65 = l_Lean_Xml_Parser_PEReference___closed__3;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_57);
x_67 = l_Lean_Xml_Parser_S(x_62);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Xml_Parser_Name(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Xml_Parser_PEDef(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
lean_inc(x_72);
x_73 = l_Lean_Xml_Parser_S(x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
lean_dec(x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_2 = x_74;
goto block_14;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
x_78 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_72, x_75);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_72);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
else
{
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
x_2 = x_72;
goto block_14;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_71, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_82 = x_71;
} else {
 lean_dec_ref(x_71);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_69, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_69, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_86 = x_69;
} else {
 lean_dec_ref(x_69);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_67, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_67, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_90 = x_67;
} else {
 lean_dec_ref(x_67);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_18);
if (x_92 == 0)
{
return x_18;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_18, 0);
x_94 = lean_ctor_get(x_18, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_18);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_16);
if (x_96 == 0)
{
return x_16;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_16, 0);
x_98 = lean_ctor_get(x_16, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_16);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 62;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_elementDecl___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EntityDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_GEDecl(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_8);
if (x_10 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Xml_Parser_PEDecl(x_1);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
x_16 = l_Lean_Xml_Parser_PEDecl(x_1);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_PublicID(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_ExternalID___closed__2;
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Xml_Parser_S(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Xml_Parser_PubidLiteral(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_7, 1, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_NotationDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<!NOTATION");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_NotationDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Xml_Parser_NotationDecl___closed__1;
x_28 = l_Lean_Parsec_pstring(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Xml_Parser_S(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Xml_Parser_Name(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_33);
x_34 = l_Lean_Xml_Parser_ExternalID(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_15 = x_35;
goto block_26;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
x_39 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_33, x_37);
if (x_39 == 0)
{
lean_dec(x_33);
return x_34;
}
else
{
lean_object* x_40; 
lean_free_object(x_34);
lean_dec(x_38);
lean_dec(x_37);
x_40 = l_Lean_Xml_Parser_PublicID(x_33);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_15 = x_41;
goto block_26;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_40);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_33, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_33);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_47);
lean_dec(x_46);
x_50 = l_Lean_Xml_Parser_PublicID(x_33);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_15 = x_51;
goto block_26;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_32);
if (x_56 == 0)
{
return x_32;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_32, 0);
x_58 = lean_ctor_get(x_32, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_32);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_30);
if (x_60 == 0)
{
return x_30;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_30, 0);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_30);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_28);
if (x_64 == 0)
{
return x_28;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_28, 0);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_28);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 62;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_elementDecl___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
block_26:
{
lean_object* x_16; 
lean_inc(x_15);
x_16 = l_Lean_Xml_Parser_S(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_17;
goto block_14;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
x_21 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_19);
if (x_21 == 0)
{
lean_dec(x_15);
return x_16;
}
else
{
lean_free_object(x_16);
lean_dec(x_20);
lean_dec(x_19);
x_2 = x_15;
goto block_14;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
else
{
lean_dec(x_23);
lean_dec(x_22);
x_2 = x_15;
goto block_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_markupDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_elementDecl(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_8);
if (x_10 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Xml_Parser_AttlistDecl(x_1);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
x_19 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_17);
if (x_19 == 0)
{
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_20; 
lean_free_object(x_11);
lean_dec(x_18);
lean_dec(x_17);
lean_inc(x_1);
x_20 = l_Lean_Xml_Parser_EntityDecl(x_1);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
x_28 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_26);
if (x_28 == 0)
{
lean_dec(x_1);
return x_20;
}
else
{
lean_object* x_29; 
lean_free_object(x_20);
lean_dec(x_27);
lean_dec(x_26);
lean_inc(x_1);
x_29 = l_Lean_Xml_Parser_NotationDecl(x_1);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
x_37 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_35);
if (x_37 == 0)
{
lean_dec(x_1);
return x_29;
}
else
{
lean_object* x_38; 
lean_free_object(x_29);
lean_dec(x_36);
lean_dec(x_35);
lean_inc(x_1);
x_38 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
x_46 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_44);
if (x_46 == 0)
{
lean_dec(x_1);
return x_38;
}
else
{
lean_object* x_47; 
lean_free_object(x_38);
lean_dec(x_45);
lean_dec(x_44);
x_47 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 1);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 1, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_38, 0);
x_59 = lean_ctor_get(x_38, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_38);
x_60 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; 
lean_dec(x_59);
lean_dec(x_58);
x_62 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_29, 0);
x_72 = lean_ctor_get(x_29, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_29);
x_73 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_71);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_1);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_72);
lean_dec(x_71);
lean_inc(x_1);
x_75 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
x_83 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_80);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_1);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
x_85 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_20, 0);
x_95 = lean_ctor_get(x_20, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_20);
x_96 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_94);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_1);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_94);
lean_inc(x_1);
x_98 = l_Lean_Xml_Parser_NotationDecl(x_1);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_1);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_105 = x_98;
} else {
 lean_dec_ref(x_98);
 x_105 = lean_box(0);
}
x_106 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_103);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_1);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
else
{
lean_object* x_108; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_inc(x_1);
x_108 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_1);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_115 = x_108;
} else {
 lean_dec_ref(x_108);
 x_115 = lean_box(0);
}
x_116 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_113);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_1);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
x_118 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_121 = lean_box(0);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_118, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_125 = x_118;
} else {
 lean_dec_ref(x_118);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_11, 0);
x_128 = lean_ctor_get(x_11, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_11);
x_129 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_127);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_1);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
else
{
lean_object* x_131; 
lean_dec(x_128);
lean_dec(x_127);
lean_inc(x_1);
x_131 = l_Lean_Xml_Parser_EntityDecl(x_1);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_1);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_131, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_138 = x_131;
} else {
 lean_dec_ref(x_131);
 x_138 = lean_box(0);
}
x_139 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_136);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_1);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
else
{
lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_inc(x_1);
x_141 = l_Lean_Xml_Parser_NotationDecl(x_1);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_1);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_141, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_148 = x_141;
} else {
 lean_dec_ref(x_141);
 x_148 = lean_box(0);
}
x_149 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_146);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_1);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_146);
lean_ctor_set(x_150, 1, x_147);
return x_150;
}
else
{
lean_object* x_151; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_inc(x_1);
x_151 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_1);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
x_159 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_156);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_1);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
else
{
lean_object* x_161; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
x_161 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_161, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_161, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_168 = x_161;
} else {
 lean_dec_ref(x_161);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_ctor_get(x_2, 0);
x_171 = lean_ctor_get(x_2, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_2);
x_172 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_170);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_1);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
else
{
lean_object* x_174; 
lean_dec(x_171);
lean_dec(x_170);
lean_inc(x_1);
x_174 = l_Lean_Xml_Parser_AttlistDecl(x_1);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_1);
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
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_179 = lean_ctor_get(x_174, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_174, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_181 = x_174;
} else {
 lean_dec_ref(x_174);
 x_181 = lean_box(0);
}
x_182 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_179);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_1);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
else
{
lean_object* x_184; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_inc(x_1);
x_184 = l_Lean_Xml_Parser_EntityDecl(x_1);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_1);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_189 = lean_ctor_get(x_184, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_191 = x_184;
} else {
 lean_dec_ref(x_184);
 x_191 = lean_box(0);
}
x_192 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_189);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_1);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_189);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
else
{
lean_object* x_194; 
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_inc(x_1);
x_194 = l_Lean_Xml_Parser_NotationDecl(x_1);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_1);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_194, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_194, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_201 = x_194;
} else {
 lean_dec_ref(x_194);
 x_201 = lean_box(0);
}
x_202 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_199);
if (x_202 == 0)
{
lean_object* x_203; 
lean_dec(x_1);
if (lean_is_scalar(x_201)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_201;
}
lean_ctor_set(x_203, 0, x_199);
lean_ctor_set(x_203, 1, x_200);
return x_203;
}
else
{
lean_object* x_204; 
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_inc(x_1);
x_204 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_1);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_209 = lean_ctor_get(x_204, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_204, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_211 = x_204;
} else {
 lean_dec_ref(x_204);
 x_211 = lean_box(0);
}
x_212 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_209);
if (x_212 == 0)
{
lean_object* x_213; 
lean_dec(x_1);
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_210);
return x_213;
}
else
{
lean_object* x_214; 
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
x_214 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
x_217 = lean_box(0);
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_216;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_214, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_221 = x_214;
} else {
 lean_dec_ref(x_214);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_DeclSep(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_PEReference(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_8);
if (x_10 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 1, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_24 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_22);
x_26 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
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
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_33 = x_26;
} else {
 lean_dec_ref(x_26);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_intSubset___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l_Lean_Xml_Parser_markupDecl(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_8);
if (x_10 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Xml_Parser_DeclSep(x_1);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
x_16 = l_Lean_Xml_Parser_DeclSep(x_1);
return x_16;
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_intSubset___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_intSubset___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_intSubset(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Xml_Parser_intSubset___closed__1;
x_3 = l_Lean_Parsec_many(lean_box(0));
x_4 = lean_apply_2(x_3, x_2, x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_4, 1, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_doctypedecl___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 91;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_doctypedecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_doctypedecl___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_doctypedecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_doctypedecl___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_doctypedecl___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 93;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_doctypedecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_doctypedecl___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_doctypedecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_doctypedecl___closed__5;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_doctypedecl___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<!DOCTYPE");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_doctypedecl(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; lean_object* x_81; lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_Xml_Parser_doctypedecl___closed__7;
x_94 = l_Lean_Parsec_pstring(x_93, x_1);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Lean_Xml_Parser_S(x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_Xml_Parser_Name(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
lean_inc(x_99);
x_100 = l_Lean_Xml_Parser_S(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_Xml_Parser_ExternalID(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
lean_dec(x_99);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_81 = x_103;
goto block_92;
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_102, 0);
x_106 = lean_ctor_get(x_102, 1);
x_107 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_99, x_105);
if (x_107 == 0)
{
lean_dec(x_99);
return x_102;
}
else
{
lean_free_object(x_102);
lean_dec(x_106);
lean_dec(x_105);
x_81 = x_99;
goto block_92;
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_102, 0);
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_102);
x_110 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_99, x_108);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_99);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_dec(x_109);
lean_dec(x_108);
x_81 = x_99;
goto block_92;
}
}
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_100);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_100, 0);
x_114 = lean_ctor_get(x_100, 1);
x_115 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_99, x_113);
if (x_115 == 0)
{
lean_dec(x_99);
return x_100;
}
else
{
lean_free_object(x_100);
lean_dec(x_114);
lean_dec(x_113);
x_81 = x_99;
goto block_92;
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_100, 0);
x_117 = lean_ctor_get(x_100, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_100);
x_118 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_99, x_116);
if (x_118 == 0)
{
lean_object* x_119; 
lean_dec(x_99);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
else
{
lean_dec(x_117);
lean_dec(x_116);
x_81 = x_99;
goto block_92;
}
}
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_98);
if (x_120 == 0)
{
return x_98;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_98, 0);
x_122 = lean_ctor_get(x_98, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_98);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_96);
if (x_124 == 0)
{
return x_96;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_96, 0);
x_126 = lean_ctor_get(x_96, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_96);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_94);
if (x_128 == 0)
{
return x_94;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_94, 0);
x_130 = lean_ctor_get(x_94, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_94);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 62;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_elementDecl___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
block_80:
{
uint32_t x_16; uint8_t x_17; 
x_16 = 91;
x_17 = l_String_Iterator_hasNext(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Parsec_unexpectedEndOfInput;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
x_2 = x_15;
goto block_14;
}
}
else
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
lean_inc(x_15);
x_21 = l_String_Iterator_next(x_15);
x_22 = l_String_Iterator_curr(x_15);
x_23 = x_22 == x_16;
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_21);
x_24 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Xml_Parser_doctypedecl___closed__3;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
x_2 = x_15;
goto block_14;
}
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Xml_Parser_intSubset(x_21);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = 93;
x_32 = l_String_Iterator_hasNext(x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_29);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_15);
x_34 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_34);
return x_27;
}
else
{
lean_free_object(x_27);
lean_dec(x_29);
x_2 = x_15;
goto block_14;
}
}
else
{
lean_object* x_35; uint32_t x_36; uint8_t x_37; 
lean_inc(x_29);
x_35 = l_String_Iterator_next(x_29);
x_36 = l_String_Iterator_curr(x_29);
x_37 = x_36 == x_31;
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_35);
x_38 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_29);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_15);
x_39 = l_Lean_Xml_Parser_doctypedecl___closed__6;
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_39);
return x_27;
}
else
{
lean_free_object(x_27);
lean_dec(x_29);
x_2 = x_15;
goto block_14;
}
}
else
{
lean_object* x_40; 
lean_free_object(x_27);
lean_dec(x_29);
lean_inc(x_35);
x_40 = l_Lean_Xml_Parser_S(x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_35);
lean_dec(x_15);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_2 = x_41;
goto block_14;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
x_45 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_35, x_43);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_35);
x_46 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_43);
if (x_46 == 0)
{
lean_dec(x_15);
return x_40;
}
else
{
lean_free_object(x_40);
lean_dec(x_44);
lean_dec(x_43);
x_2 = x_15;
goto block_14;
}
}
else
{
lean_free_object(x_40);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_15);
x_2 = x_35;
goto block_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
x_49 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_35, x_47);
if (x_49 == 0)
{
uint8_t x_50; 
lean_dec(x_35);
x_50 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_47);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_15);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
else
{
lean_dec(x_48);
lean_dec(x_47);
x_2 = x_15;
goto block_14;
}
}
else
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_15);
x_2 = x_35;
goto block_14;
}
}
}
}
}
}
else
{
lean_object* x_52; uint32_t x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_27, 0);
lean_inc(x_52);
lean_dec(x_27);
x_53 = 93;
x_54 = l_String_Iterator_hasNext(x_52);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_15);
x_56 = l_Lean_Parsec_unexpectedEndOfInput;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_dec(x_52);
x_2 = x_15;
goto block_14;
}
}
else
{
lean_object* x_58; uint32_t x_59; uint8_t x_60; 
lean_inc(x_52);
x_58 = l_String_Iterator_next(x_52);
x_59 = l_String_Iterator_curr(x_52);
x_60 = x_59 == x_53;
if (x_60 == 0)
{
uint8_t x_61; 
lean_dec(x_58);
x_61 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_52);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_15);
x_62 = l_Lean_Xml_Parser_doctypedecl___closed__6;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
else
{
lean_dec(x_52);
x_2 = x_15;
goto block_14;
}
}
else
{
lean_object* x_64; 
lean_dec(x_52);
lean_inc(x_58);
x_64 = l_Lean_Xml_Parser_S(x_58);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_15);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
x_2 = x_65;
goto block_14;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
x_69 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_58, x_66);
if (x_69 == 0)
{
uint8_t x_70; 
lean_dec(x_58);
x_70 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_66);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_15);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
else
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
x_2 = x_15;
goto block_14;
}
}
else
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_15);
x_2 = x_58;
goto block_14;
}
}
}
}
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_27);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_27, 0);
x_74 = lean_ctor_get(x_27, 1);
x_75 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_73);
if (x_75 == 0)
{
lean_dec(x_15);
return x_27;
}
else
{
lean_free_object(x_27);
lean_dec(x_74);
lean_dec(x_73);
x_2 = x_15;
goto block_14;
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_27, 0);
x_77 = lean_ctor_get(x_27, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_27);
x_78 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_15, x_76);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_15);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_dec(x_77);
lean_dec(x_76);
x_2 = x_15;
goto block_14;
}
}
}
}
}
}
block_92:
{
lean_object* x_82; 
lean_inc(x_81);
x_82 = l_Lean_Xml_Parser_S(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_15 = x_83;
goto block_80;
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
x_87 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_81, x_85);
if (x_87 == 0)
{
lean_dec(x_81);
return x_82;
}
else
{
lean_free_object(x_82);
lean_dec(x_86);
lean_dec(x_85);
x_15 = x_81;
goto block_80;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_82, 0);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_82);
x_90 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_81, x_88);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_81);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_dec(x_89);
lean_dec(x_88);
x_15 = x_81;
goto block_80;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_prolog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_Misc), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_prolog(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_44; 
lean_inc(x_1);
x_44 = l_Lean_Xml_Parser_XMLdecl(x_1);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_1);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_2 = x_45;
goto block_43;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
x_49 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_47);
if (x_49 == 0)
{
lean_dec(x_1);
return x_44;
}
else
{
lean_free_object(x_44);
lean_dec(x_48);
lean_dec(x_47);
x_2 = x_1;
goto block_43;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_1);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_dec(x_51);
lean_dec(x_50);
x_2 = x_1;
goto block_43;
}
}
}
block_43:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Xml_Parser_prolog___closed__1;
x_4 = l_Lean_Parsec_many(lean_box(0));
x_5 = lean_apply_2(x_4, x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_6);
x_7 = l_Lean_Xml_Parser_doctypedecl(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Parsec_many(lean_box(0));
x_10 = lean_apply_2(x_9, x_3, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
x_20 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_6, x_18);
if (x_20 == 0)
{
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_box(0);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_21);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_6, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_7, 0);
x_30 = lean_ctor_get(x_7, 1);
x_31 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_6, x_29);
if (x_31 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_29);
x_32 = lean_box(0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_32);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_6, x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_6);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_5);
if (x_39 == 0)
{
return x_5;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_Attribute(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_Name(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Xml_Parser_Eq(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Xml_Parser_AttValue(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_7, 1, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_4);
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
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
return x_2;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_string_dec_lt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_string_dec_eq(x_2, x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_12, x_2, x_3);
x_16 = 0;
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_string_dec_lt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_string_dec_eq(x_2, x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_23, x_2, x_3);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_21);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_string_dec_lt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_string_dec_eq(x_2, x_36);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Std_RBNode_isRed___rarg(x_38);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_38, x_2, x_3);
x_43 = 1;
lean_ctor_set(x_1, 3, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_38, x_2, x_3);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 3);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_44, 3);
lean_dec(x_48);
x_49 = lean_ctor_get(x_44, 0);
lean_dec(x_49);
x_50 = 0;
lean_ctor_set(x_44, 0, x_46);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_50);
x_51 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_51);
return x_1;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_44, 1);
x_53 = lean_ctor_get(x_44, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = 0;
x_55 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_54);
x_56 = 1;
lean_ctor_set(x_1, 3, x_55);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_44);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_44, 1);
x_60 = lean_ctor_get(x_44, 2);
x_61 = lean_ctor_get(x_44, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_44, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_46);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_46, 0);
x_65 = lean_ctor_get(x_46, 1);
x_66 = lean_ctor_get(x_46, 2);
x_67 = lean_ctor_get(x_46, 3);
x_68 = 1;
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_68);
lean_ctor_set(x_44, 3, x_67);
lean_ctor_set(x_44, 2, x_66);
lean_ctor_set(x_44, 1, x_65);
lean_ctor_set(x_44, 0, x_64);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_68);
x_69 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_60);
lean_ctor_set(x_1, 1, x_59);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_46, 0);
x_71 = lean_ctor_get(x_46, 1);
x_72 = lean_ctor_get(x_46, 2);
x_73 = lean_ctor_get(x_46, 3);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_46);
x_74 = 1;
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_35);
lean_ctor_set(x_75, 1, x_36);
lean_ctor_set(x_75, 2, x_37);
lean_ctor_set(x_75, 3, x_45);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
lean_ctor_set(x_44, 3, x_73);
lean_ctor_set(x_44, 2, x_72);
lean_ctor_set(x_44, 1, x_71);
lean_ctor_set(x_44, 0, x_70);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_74);
x_76 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_60);
lean_ctor_set(x_1, 1, x_59);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_76);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_77 = lean_ctor_get(x_44, 1);
x_78 = lean_ctor_get(x_44, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_44);
x_79 = lean_ctor_get(x_46, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_46, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_46, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_46, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_83 = x_46;
} else {
 lean_dec_ref(x_46);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_36);
lean_ctor_set(x_85, 2, x_37);
lean_ctor_set(x_85, 3, x_45);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
x_87 = 0;
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_87);
return x_1;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_44);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_44, 3);
lean_dec(x_89);
x_90 = lean_ctor_get(x_44, 0);
lean_dec(x_90);
x_91 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_91);
x_92 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_44, 1);
x_94 = lean_ctor_get(x_44, 2);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_44);
x_95 = 0;
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_45);
lean_ctor_set(x_96, 1, x_93);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_96, 3, x_46);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_95);
x_97 = 1;
lean_ctor_set(x_1, 3, x_96);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
}
}
}
else
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_45, sizeof(void*)*4);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_44);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_44, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_45);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; 
x_102 = lean_ctor_get(x_45, 0);
x_103 = lean_ctor_get(x_45, 1);
x_104 = lean_ctor_get(x_45, 2);
x_105 = lean_ctor_get(x_45, 3);
x_106 = 1;
lean_ctor_set(x_45, 3, x_102);
lean_ctor_set(x_45, 2, x_37);
lean_ctor_set(x_45, 1, x_36);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_106);
lean_ctor_set(x_44, 0, x_105);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_106);
x_107 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_104);
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_107);
return x_1;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; uint8_t x_114; 
x_108 = lean_ctor_get(x_45, 0);
x_109 = lean_ctor_get(x_45, 1);
x_110 = lean_ctor_get(x_45, 2);
x_111 = lean_ctor_get(x_45, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_45);
x_112 = 1;
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_35);
lean_ctor_set(x_113, 1, x_36);
lean_ctor_set(x_113, 2, x_37);
lean_ctor_set(x_113, 3, x_108);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_112);
lean_ctor_set(x_44, 0, x_111);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_112);
x_114 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_110);
lean_ctor_set(x_1, 1, x_109);
lean_ctor_set(x_1, 0, x_113);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_114);
return x_1;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_115 = lean_ctor_get(x_44, 1);
x_116 = lean_ctor_get(x_44, 2);
x_117 = lean_ctor_get(x_44, 3);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_44);
x_118 = lean_ctor_get(x_45, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_45, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_45, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_45, 3);
lean_inc(x_121);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_122 = x_45;
} else {
 lean_dec_ref(x_45);
 x_122 = lean_box(0);
}
x_123 = 1;
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(1, 4, 1);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_35);
lean_ctor_set(x_124, 1, x_36);
lean_ctor_set(x_124, 2, x_37);
lean_ctor_set(x_124, 3, x_118);
lean_ctor_set_uint8(x_124, sizeof(void*)*4, x_123);
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_115);
lean_ctor_set(x_125, 2, x_116);
lean_ctor_set(x_125, 3, x_117);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_123);
x_126 = 0;
lean_ctor_set(x_1, 3, x_125);
lean_ctor_set(x_1, 2, x_120);
lean_ctor_set(x_1, 1, x_119);
lean_ctor_set(x_1, 0, x_124);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_126);
return x_1;
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_44, 3);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_44);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_44, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_44, 0);
lean_dec(x_130);
x_131 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_131);
x_132 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_132);
return x_1;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_44, 1);
x_134 = lean_ctor_get(x_44, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_44);
x_135 = 0;
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_45);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_127);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
x_137 = 1;
lean_ctor_set(x_1, 3, x_136);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
}
else
{
uint8_t x_138; 
x_138 = lean_ctor_get_uint8(x_127, sizeof(void*)*4);
if (x_138 == 0)
{
uint8_t x_139; 
lean_free_object(x_1);
x_139 = !lean_is_exclusive(x_44);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = lean_ctor_get(x_44, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_44, 0);
lean_dec(x_141);
x_142 = !lean_is_exclusive(x_127);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; 
x_143 = lean_ctor_get(x_127, 0);
x_144 = lean_ctor_get(x_127, 1);
x_145 = lean_ctor_get(x_127, 2);
x_146 = lean_ctor_get(x_127, 3);
x_147 = 1;
lean_inc(x_45);
lean_ctor_set(x_127, 3, x_45);
lean_ctor_set(x_127, 2, x_37);
lean_ctor_set(x_127, 1, x_36);
lean_ctor_set(x_127, 0, x_35);
x_148 = !lean_is_exclusive(x_45);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_45, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_45, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_45, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_45, 0);
lean_dec(x_152);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_147);
lean_ctor_set(x_45, 3, x_146);
lean_ctor_set(x_45, 2, x_145);
lean_ctor_set(x_45, 1, x_144);
lean_ctor_set(x_45, 0, x_143);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_147);
x_153 = 0;
lean_ctor_set(x_44, 3, x_45);
lean_ctor_set(x_44, 0, x_127);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_153);
return x_44;
}
else
{
lean_object* x_154; uint8_t x_155; 
lean_dec(x_45);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_147);
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_144);
lean_ctor_set(x_154, 2, x_145);
lean_ctor_set(x_154, 3, x_146);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_147);
x_155 = 0;
lean_ctor_set(x_44, 3, x_154);
lean_ctor_set(x_44, 0, x_127);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_155);
return x_44;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_156 = lean_ctor_get(x_127, 0);
x_157 = lean_ctor_get(x_127, 1);
x_158 = lean_ctor_get(x_127, 2);
x_159 = lean_ctor_get(x_127, 3);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_127);
x_160 = 1;
lean_inc(x_45);
x_161 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_161, 0, x_35);
lean_ctor_set(x_161, 1, x_36);
lean_ctor_set(x_161, 2, x_37);
lean_ctor_set(x_161, 3, x_45);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_162 = x_45;
} else {
 lean_dec_ref(x_45);
 x_162 = lean_box(0);
}
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_160);
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_157);
lean_ctor_set(x_163, 2, x_158);
lean_ctor_set(x_163, 3, x_159);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_160);
x_164 = 0;
lean_ctor_set(x_44, 3, x_163);
lean_ctor_set(x_44, 0, x_161);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_164);
return x_44;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_165 = lean_ctor_get(x_44, 1);
x_166 = lean_ctor_get(x_44, 2);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_44);
x_167 = lean_ctor_get(x_127, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_127, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_127, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_127, 3);
lean_inc(x_170);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 x_171 = x_127;
} else {
 lean_dec_ref(x_127);
 x_171 = lean_box(0);
}
x_172 = 1;
lean_inc(x_45);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_35);
lean_ctor_set(x_173, 1, x_36);
lean_ctor_set(x_173, 2, x_37);
lean_ctor_set(x_173, 3, x_45);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_174 = x_45;
} else {
 lean_dec_ref(x_45);
 x_174 = lean_box(0);
}
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 4, 1);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_167);
lean_ctor_set(x_175, 1, x_168);
lean_ctor_set(x_175, 2, x_169);
lean_ctor_set(x_175, 3, x_170);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_172);
x_176 = 0;
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_165);
lean_ctor_set(x_177, 2, x_166);
lean_ctor_set(x_177, 3, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_176);
return x_177;
}
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_44);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_44, 3);
lean_dec(x_179);
x_180 = lean_ctor_get(x_44, 0);
lean_dec(x_180);
x_181 = !lean_is_exclusive(x_45);
if (x_181 == 0)
{
uint8_t x_182; uint8_t x_183; 
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_138);
x_182 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_182);
x_183 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; 
x_184 = lean_ctor_get(x_45, 0);
x_185 = lean_ctor_get(x_45, 1);
x_186 = lean_ctor_get(x_45, 2);
x_187 = lean_ctor_get(x_45, 3);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_45);
x_188 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_186);
lean_ctor_set(x_188, 3, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_138);
x_189 = 0;
lean_ctor_set(x_44, 0, x_188);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_189);
x_190 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; uint8_t x_201; 
x_191 = lean_ctor_get(x_44, 1);
x_192 = lean_ctor_get(x_44, 2);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_44);
x_193 = lean_ctor_get(x_45, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_45, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_45, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_45, 3);
lean_inc(x_196);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_197 = x_45;
} else {
 lean_dec_ref(x_45);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 4, 1);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_194);
lean_ctor_set(x_198, 2, x_195);
lean_ctor_set(x_198, 3, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_138);
x_199 = 0;
x_200 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_191);
lean_ctor_set(x_200, 2, x_192);
lean_ctor_set(x_200, 3, x_127);
lean_ctor_set_uint8(x_200, sizeof(void*)*4, x_199);
x_201 = 1;
lean_ctor_set(x_1, 3, x_200);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_201);
return x_1;
}
}
}
}
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_37);
lean_dec(x_36);
x_202 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
x_369 = lean_string_dec_lt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
x_370 = lean_string_dec_eq(x_2, x_366);
if (x_370 == 0)
{
uint8_t x_371; 
x_371 = l_Std_RBNode_isRed___rarg(x_368);
if (x_371 == 0)
{
lean_object* x_372; uint8_t x_373; lean_object* x_374; 
x_372 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_368, x_2, x_3);
x_373 = 1;
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_365);
lean_ctor_set(x_374, 1, x_366);
lean_ctor_set(x_374, 2, x_367);
lean_ctor_set(x_374, 3, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_368, x_2, x_3);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_375, 3);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; 
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_375, 2);
lean_inc(x_379);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_380 = x_375;
} else {
 lean_dec_ref(x_375);
 x_380 = lean_box(0);
}
x_381 = 0;
if (lean_is_scalar(x_380)) {
 x_382 = lean_alloc_ctor(1, 4, 1);
} else {
 x_382 = x_380;
}
lean_ctor_set(x_382, 0, x_377);
lean_ctor_set(x_382, 1, x_378);
lean_ctor_set(x_382, 2, x_379);
lean_ctor_set(x_382, 3, x_377);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_381);
x_383 = 1;
x_384 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_384, 0, x_365);
lean_ctor_set(x_384, 1, x_366);
lean_ctor_set(x_384, 2, x_367);
lean_ctor_set(x_384, 3, x_382);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
return x_384;
}
else
{
uint8_t x_385; 
x_385 = lean_ctor_get_uint8(x_377, sizeof(void*)*4);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; 
x_386 = lean_ctor_get(x_375, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_375, 2);
lean_inc(x_387);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_388 = x_375;
} else {
 lean_dec_ref(x_375);
 x_388 = lean_box(0);
}
x_389 = lean_ctor_get(x_377, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_377, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_377, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_377, 3);
lean_inc(x_392);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_393 = x_377;
} else {
 lean_dec_ref(x_377);
 x_393 = lean_box(0);
}
x_394 = 1;
if (lean_is_scalar(x_393)) {
 x_395 = lean_alloc_ctor(1, 4, 1);
} else {
 x_395 = x_393;
}
lean_ctor_set(x_395, 0, x_365);
lean_ctor_set(x_395, 1, x_366);
lean_ctor_set(x_395, 2, x_367);
lean_ctor_set(x_395, 3, x_376);
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_394);
if (lean_is_scalar(x_388)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_388;
}
lean_ctor_set(x_396, 0, x_389);
lean_ctor_set(x_396, 1, x_390);
lean_ctor_set(x_396, 2, x_391);
lean_ctor_set(x_396, 3, x_392);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_394);
x_397 = 0;
x_398 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_386);
lean_ctor_set(x_398, 2, x_387);
lean_ctor_set(x_398, 3, x_396);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_397);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; 
x_399 = lean_ctor_get(x_375, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_375, 2);
lean_inc(x_400);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_401 = x_375;
} else {
 lean_dec_ref(x_375);
 x_401 = lean_box(0);
}
x_402 = 0;
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_376);
lean_ctor_set(x_403, 1, x_399);
lean_ctor_set(x_403, 2, x_400);
lean_ctor_set(x_403, 3, x_377);
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
x_404 = 1;
x_405 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_405, 0, x_365);
lean_ctor_set(x_405, 1, x_366);
lean_ctor_set(x_405, 2, x_367);
lean_ctor_set(x_405, 3, x_403);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
return x_405;
}
}
}
else
{
uint8_t x_406; 
x_406 = lean_ctor_get_uint8(x_376, sizeof(void*)*4);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; 
x_407 = lean_ctor_get(x_375, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_375, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_375, 3);
lean_inc(x_409);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_410 = x_375;
} else {
 lean_dec_ref(x_375);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_376, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_376, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_376, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_376, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_415 = x_376;
} else {
 lean_dec_ref(x_376);
 x_415 = lean_box(0);
}
x_416 = 1;
if (lean_is_scalar(x_415)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_415;
}
lean_ctor_set(x_417, 0, x_365);
lean_ctor_set(x_417, 1, x_366);
lean_ctor_set(x_417, 2, x_367);
lean_ctor_set(x_417, 3, x_411);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_416);
if (lean_is_scalar(x_410)) {
 x_418 = lean_alloc_ctor(1, 4, 1);
} else {
 x_418 = x_410;
}
lean_ctor_set(x_418, 0, x_414);
lean_ctor_set(x_418, 1, x_407);
lean_ctor_set(x_418, 2, x_408);
lean_ctor_set(x_418, 3, x_409);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_416);
x_419 = 0;
x_420 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_412);
lean_ctor_set(x_420, 2, x_413);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_419);
return x_420;
}
else
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_375, 3);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; 
x_422 = lean_ctor_get(x_375, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_375, 2);
lean_inc(x_423);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_424 = x_375;
} else {
 lean_dec_ref(x_375);
 x_424 = lean_box(0);
}
x_425 = 0;
if (lean_is_scalar(x_424)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_424;
}
lean_ctor_set(x_426, 0, x_376);
lean_ctor_set(x_426, 1, x_422);
lean_ctor_set(x_426, 2, x_423);
lean_ctor_set(x_426, 3, x_421);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = 1;
x_428 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_428, 0, x_365);
lean_ctor_set(x_428, 1, x_366);
lean_ctor_set(x_428, 2, x_367);
lean_ctor_set(x_428, 3, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
return x_428;
}
else
{
uint8_t x_429; 
x_429 = lean_ctor_get_uint8(x_421, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; 
x_430 = lean_ctor_get(x_375, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_375, 2);
lean_inc(x_431);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_432 = x_375;
} else {
 lean_dec_ref(x_375);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_421, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_421, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_421, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_421, 3);
lean_inc(x_436);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 lean_ctor_release(x_421, 2);
 lean_ctor_release(x_421, 3);
 x_437 = x_421;
} else {
 lean_dec_ref(x_421);
 x_437 = lean_box(0);
}
x_438 = 1;
lean_inc(x_376);
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_365);
lean_ctor_set(x_439, 1, x_366);
lean_ctor_set(x_439, 2, x_367);
lean_ctor_set(x_439, 3, x_376);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_440 = x_376;
} else {
 lean_dec_ref(x_376);
 x_440 = lean_box(0);
}
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_433);
lean_ctor_set(x_441, 1, x_434);
lean_ctor_set(x_441, 2, x_435);
lean_ctor_set(x_441, 3, x_436);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_438);
x_442 = 0;
if (lean_is_scalar(x_432)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_432;
}
lean_ctor_set(x_443, 0, x_439);
lean_ctor_set(x_443, 1, x_430);
lean_ctor_set(x_443, 2, x_431);
lean_ctor_set(x_443, 3, x_441);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; 
x_444 = lean_ctor_get(x_375, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_375, 2);
lean_inc(x_445);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_446 = x_375;
} else {
 lean_dec_ref(x_375);
 x_446 = lean_box(0);
}
x_447 = lean_ctor_get(x_376, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_376, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_376, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_376, 3);
lean_inc(x_450);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_451 = x_376;
} else {
 lean_dec_ref(x_376);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 4, 1);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_447);
lean_ctor_set(x_452, 1, x_448);
lean_ctor_set(x_452, 2, x_449);
lean_ctor_set(x_452, 3, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_429);
x_453 = 0;
if (lean_is_scalar(x_446)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_446;
}
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_444);
lean_ctor_set(x_454, 2, x_445);
lean_ctor_set(x_454, 3, x_421);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
x_455 = 1;
x_456 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_456, 0, x_365);
lean_ctor_set(x_456, 1, x_366);
lean_ctor_set(x_456, 2, x_367);
lean_ctor_set(x_456, 3, x_454);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
return x_456;
}
}
}
}
}
}
else
{
uint8_t x_457; lean_object* x_458; 
lean_dec(x_367);
lean_dec(x_366);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_2);
lean_ctor_set(x_458, 2, x_3);
lean_ctor_set(x_458, 3, x_368);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__2(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Std_RBNode_insert___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__1(x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__3___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Std_RBNode_insert___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__1(x_1, x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_elementPrefix___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_to_list(lean_box(0), x_2);
x_5 = lean_box(0);
x_6 = l_List_foldl___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__3___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__4(x_5, x_4);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_elementPrefix___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_S(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Xml_Parser_Attribute(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_elementPrefix___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 60;
x_2 = l_Lean_Xml_Parser_endl___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_elementPrefix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_endl___closed__3;
x_2 = l_Lean_Xml_Parser_elementPrefix___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_elementPrefix___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Xml_Parser_elementPrefix___closed__2;
x_2 = l_Lean_Xml_Parser_endl___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Xml_Parser_elementPrefix___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_elementPrefix___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_elementPrefix(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 60;
x_3 = l_String_Iterator_hasNext(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parsec_unexpectedEndOfInput;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint32_t x_7; uint8_t x_8; 
lean_inc(x_1);
x_6 = l_String_Iterator_next(x_1);
x_7 = l_String_Iterator_curr(x_1);
x_8 = x_7 == x_2;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = l_Lean_Xml_Parser_elementPrefix___closed__3;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Xml_Parser_Name(x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Xml_Parser_elementPrefix___closed__4;
x_15 = l_Lean_Parsec_many(lean_box(0));
x_16 = lean_apply_2(x_15, x_14, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = l_Lean_Xml_Parser_S(x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 1);
lean_dec(x_21);
x_22 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_elementPrefix___elambda__1), 3, 2);
lean_closure_set(x_22, 0, x_13);
lean_closure_set(x_22, 1, x_18);
lean_ctor_set(x_19, 1, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_elementPrefix___elambda__1), 3, 2);
lean_closure_set(x_24, 0, x_13);
lean_closure_set(x_24, 1, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
x_29 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_17, x_27);
if (x_29 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
return x_19;
}
else
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_elementPrefix___elambda__1), 3, 2);
lean_closure_set(x_30, 0, x_13);
lean_closure_set(x_30, 1, x_18);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 1, x_30);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_17, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_31);
x_35 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_elementPrefix___elambda__1), 3, 2);
lean_closure_set(x_35, 0, x_13);
lean_closure_set(x_35, 1, x_18);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_13);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at_Lean_Xml_Parser_elementPrefix___elambda__1___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EmptyElemTag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("/>");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_EmptyElemTag___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_EmptyElemTag(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Xml_Parser_EmptyElemTag___closed__1;
x_4 = l_Lean_Parsec_pstring(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_dec(x_6);
x_7 = l_Lean_Xml_Parser_EmptyElemTag___closed__2;
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_4, 1, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_Xml_Parser_EmptyElemTag___closed__2;
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_STag(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 62;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_1);
x_10 = l_Lean_Xml_Parser_elementDecl___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_1);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_ETag___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("</");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_ETag(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Xml_Parser_ETag___closed__1;
x_16 = l_Lean_Parsec_pstring(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Xml_Parser_Name(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_19);
x_20 = l_Lean_Xml_Parser_S(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_2 = x_21;
goto block_14;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
x_25 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_19, x_23);
if (x_25 == 0)
{
lean_dec(x_19);
return x_20;
}
else
{
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_23);
x_2 = x_19;
goto block_14;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_19, x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
else
{
lean_dec(x_27);
lean_dec(x_26);
x_2 = x_19;
goto block_14;
}
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
block_14:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 62;
x_4 = l_String_Iterator_hasNext(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parsec_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; 
lean_inc(x_2);
x_7 = l_String_Iterator_next(x_2);
x_8 = l_String_Iterator_curr(x_2);
x_9 = x_8 == x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = l_Lean_Xml_Parser_elementDecl___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_CDStart___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<![CDATA[");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CDStart(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_CDStart___closed__1;
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_CDEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]]>");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CDEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_CDEnd___closed__1;
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CData___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_CDEnd___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_Xml_Parser_endl___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = l_Lean_Xml_Parser_endl___closed__1;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = l_String_Iterator_hasNext(x_1);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Parsec_unexpectedEndOfInput;
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_15; uint32_t x_16; lean_object* x_17; 
lean_inc(x_1);
x_15 = l_String_Iterator_next(x_1);
x_16 = l_String_Iterator_curr(x_1);
lean_dec(x_1);
x_17 = lean_box_uint32(x_16);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
}
else
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = l_String_Iterator_hasNext(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Parsec_unexpectedEndOfInput;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; uint32_t x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_1);
x_21 = l_String_Iterator_next(x_1);
x_22 = l_String_Iterator_curr(x_1);
lean_dec(x_1);
x_23 = lean_box_uint32(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_CData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_CData___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_CData___closed__1;
x_3 = l_Lean_Parsec_manyChars(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CDSect(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_CDStart(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Xml_Parser_CData(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Xml_Parser_CDEnd(x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 1);
lean_dec(x_9);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
return x_2;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Xml_Parser_CharData___lambda__1(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = 60;
x_3 = x_1 == x_2;
x_4 = l_instDecidableNot___rarg(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint32_t x_6; uint8_t x_7; uint8_t x_8; 
x_6 = 38;
x_7 = x_1 == x_6;
x_8 = l_instDecidableNot___rarg(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_CharData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_CharData___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_CharData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Xml_Parser_CharData___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parsec_satisfy), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CharData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Xml_Parser_CDEnd___closed__1;
lean_inc(x_1);
x_3 = l_Lean_Parsec_pstring(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_Xml_Parser_endl___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = l_Lean_Xml_Parser_endl___closed__1;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = l_Lean_Xml_Parser_CharData___closed__2;
x_11 = l_Lean_Parsec_manyChars(x_10, x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_CharData___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Xml_Parser_CharData___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_back___at_Lean_Xml_Parser_content___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Xml_instInhabitedContent;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = x_2 + x_7;
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_array_push(x_4, x_10);
x_2 = x_8;
x_4 = x_11;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Xml_Parser_content___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = l_Lean_Xml_Parser_EmptyElemTag___closed__2;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_Xml_Parser_EmptyElemTag___closed__2;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Lean_Xml_Parser_EmptyElemTag___closed__2;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__3(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Xml_Parser_content___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_13; 
x_13 = x_3 < x_2;
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = lean_array_get_size(x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = lean_array_push(x_4, x_15);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_6 = x_5;
x_7 = x_20;
goto block_12;
}
else
{
lean_object* x_21; 
x_21 = l_Array_back___at_Lean_Xml_Parser_content___spec__1(x_4);
if (lean_obj_tag(x_21) == 2)
{
if (lean_obj_tag(x_15) == 2)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_16, x_25);
lean_dec(x_16);
x_27 = lean_string_append(x_22, x_24);
lean_dec(x_24);
lean_ctor_set(x_15, 0, x_27);
x_28 = lean_array_set(x_4, x_26, x_15);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_6 = x_5;
x_7 = x_29;
goto block_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_16, x_31);
lean_dec(x_16);
x_33 = lean_string_append(x_22, x_30);
lean_dec(x_30);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_array_set(x_4, x_32, x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_6 = x_5;
x_7 = x_36;
goto block_12;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_21);
lean_dec(x_16);
x_37 = lean_array_push(x_4, x_15);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_6 = x_5;
x_7 = x_38;
goto block_12;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_21);
lean_dec(x_16);
x_39 = lean_array_push(x_4, x_15);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_6 = x_5;
x_7 = x_40;
goto block_12;
}
}
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_4 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_append___rarg(x_4, x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_content___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_content___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_38; 
lean_inc(x_1);
x_38 = l_Lean_Xml_Parser_element(x_1);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_2 = x_39;
x_3 = x_42;
goto block_37;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_38, 1);
x_45 = lean_ctor_get(x_38, 0);
lean_dec(x_45);
x_46 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_1);
if (x_46 == 0)
{
lean_ctor_set(x_38, 0, x_1);
return x_38;
}
else
{
lean_object* x_47; 
lean_free_object(x_38);
lean_dec(x_44);
lean_inc(x_1);
x_47 = l_Lean_Xml_Parser_Reference(x_1);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_box(0);
x_2 = x_49;
x_3 = x_50;
goto block_37;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec(x_47);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint32_t x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = l_Lean_Xml_Parser_endl___closed__1;
x_55 = lean_unbox_uint32(x_53);
lean_dec(x_53);
x_56 = lean_string_push(x_54, x_55);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_48, 0, x_57);
x_2 = x_51;
x_3 = x_48;
goto block_37;
}
else
{
lean_object* x_58; lean_object* x_59; uint32_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_48, 0);
lean_inc(x_58);
lean_dec(x_48);
x_59 = l_Lean_Xml_Parser_endl___closed__1;
x_60 = lean_unbox_uint32(x_58);
lean_dec(x_58);
x_61 = lean_string_push(x_59, x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_2 = x_51;
x_3 = x_63;
goto block_37;
}
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_65);
if (x_67 == 0)
{
lean_dec(x_1);
return x_47;
}
else
{
lean_object* x_68; 
lean_free_object(x_47);
lean_dec(x_66);
lean_dec(x_65);
lean_inc(x_1);
x_68 = l_Lean_Xml_Parser_CDSect(x_1);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_2 = x_69;
x_3 = x_72;
goto block_37;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_68, 0);
x_75 = lean_ctor_get(x_68, 1);
x_76 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_74);
if (x_76 == 0)
{
lean_dec(x_1);
return x_68;
}
else
{
lean_object* x_77; 
lean_free_object(x_68);
lean_dec(x_75);
lean_dec(x_74);
lean_inc(x_1);
x_77 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_box(0);
x_2 = x_78;
x_3 = x_79;
goto block_37;
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
x_83 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_81);
if (x_83 == 0)
{
lean_dec(x_1);
return x_77;
}
else
{
lean_object* x_84; 
lean_free_object(x_77);
lean_dec(x_82);
lean_dec(x_81);
x_84 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_2 = x_85;
x_3 = x_88;
goto block_37;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
return x_84;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_77, 0);
x_94 = lean_ctor_get(x_77, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_77);
x_95 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_93);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
else
{
lean_object* x_97; 
lean_dec(x_94);
lean_dec(x_93);
x_97 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_2 = x_98;
x_3 = x_101;
goto block_37;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_104 = x_97;
} else {
 lean_dec_ref(x_97);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_68, 0);
x_107 = lean_ctor_get(x_68, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_68);
x_108 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_106);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_1);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; 
lean_dec(x_107);
lean_dec(x_106);
lean_inc(x_1);
x_110 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_1);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_box(0);
x_2 = x_111;
x_3 = x_112;
goto block_37;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_115 = x_110;
} else {
 lean_dec_ref(x_110);
 x_115 = lean_box(0);
}
x_116 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_113);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_1);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
x_118 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_2 = x_119;
x_3 = x_122;
goto block_37;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_118, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_125 = x_118;
} else {
 lean_dec_ref(x_118);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
}
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_47, 0);
x_128 = lean_ctor_get(x_47, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_47);
x_129 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_127);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_1);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
else
{
lean_object* x_131; 
lean_dec(x_128);
lean_dec(x_127);
lean_inc(x_1);
x_131 = l_Lean_Xml_Parser_CDSect(x_1);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_1);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_2 = x_132;
x_3 = x_135;
goto block_37;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_131, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_138 = x_131;
} else {
 lean_dec_ref(x_131);
 x_138 = lean_box(0);
}
x_139 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_136);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_1);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
else
{
lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_inc(x_1);
x_141 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_1);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec(x_141);
x_143 = lean_box(0);
x_2 = x_142;
x_3 = x_143;
goto block_37;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_146 = x_141;
} else {
 lean_dec_ref(x_141);
 x_146 = lean_box(0);
}
x_147 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_144);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_1);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
else
{
lean_object* x_149; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
x_149 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_2 = x_150;
x_3 = x_153;
goto block_37;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_149, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_156 = x_149;
} else {
 lean_dec_ref(x_149);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_38, 1);
lean_inc(x_158);
lean_dec(x_38);
x_159 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_1);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_1);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
else
{
lean_object* x_161; 
lean_dec(x_158);
lean_inc(x_1);
x_161 = l_Lean_Xml_Parser_Reference(x_1);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
lean_dec(x_1);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_box(0);
x_2 = x_163;
x_3 = x_164;
goto block_37;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint32_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_161, 0);
lean_inc(x_165);
lean_dec(x_161);
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_167 = x_162;
} else {
 lean_dec_ref(x_162);
 x_167 = lean_box(0);
}
x_168 = l_Lean_Xml_Parser_endl___closed__1;
x_169 = lean_unbox_uint32(x_166);
lean_dec(x_166);
x_170 = lean_string_push(x_168, x_169);
x_171 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_171, 0, x_170);
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(1, 1, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_171);
x_2 = x_165;
x_3 = x_172;
goto block_37;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_173 = lean_ctor_get(x_161, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_161, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_175 = x_161;
} else {
 lean_dec_ref(x_161);
 x_175 = lean_box(0);
}
x_176 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_173);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_1);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
return x_177;
}
else
{
lean_object* x_178; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_inc(x_1);
x_178 = l_Lean_Xml_Parser_CDSect(x_1);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_1);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_2 = x_179;
x_3 = x_182;
goto block_37;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_183 = lean_ctor_get(x_178, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_178, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_185 = x_178;
} else {
 lean_dec_ref(x_178);
 x_185 = lean_box(0);
}
x_186 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_183);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec(x_1);
if (lean_is_scalar(x_185)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_185;
}
lean_ctor_set(x_187, 0, x_183);
lean_ctor_set(x_187, 1, x_184);
return x_187;
}
else
{
lean_object* x_188; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_inc(x_1);
x_188 = l_Lean_Xml_Parser_PI(x_1);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_1);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_box(0);
x_2 = x_189;
x_3 = x_190;
goto block_37;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_193 = x_188;
} else {
 lean_dec_ref(x_188);
 x_193 = lean_box(0);
}
x_194 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_191);
if (x_194 == 0)
{
lean_object* x_195; 
lean_dec(x_1);
if (lean_is_scalar(x_193)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_193;
}
lean_ctor_set(x_195, 0, x_191);
lean_ctor_set(x_195, 1, x_192);
return x_195;
}
else
{
lean_object* x_196; 
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
x_196 = l_Lean_Xml_Parser_Comment(x_1);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_2 = x_197;
x_3 = x_200;
goto block_37;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_196, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_203 = x_196;
} else {
 lean_dec_ref(x_196);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
}
}
}
}
}
}
}
block_37:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Xml_Parser_CharData(x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Xml_Parser_content___lambda__1___closed__1;
x_10 = lean_array_push(x_9, x_3);
x_11 = lean_array_push(x_10, x_8);
lean_ctor_set(x_4, 1, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Xml_Parser_content___lambda__1___closed__1;
x_17 = lean_array_push(x_16, x_3);
x_18 = lean_array_push(x_17, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_21);
if (x_23 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = l_Lean_Xml_Parser_content___lambda__1___closed__1;
x_26 = lean_array_push(x_25, x_3);
x_27 = lean_array_push(x_26, x_24);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_2, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_29);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l_Lean_Xml_Parser_content___lambda__1___closed__1;
x_34 = lean_array_push(x_33, x_3);
x_35 = lean_array_push(x_34, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Xml_Parser_content___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Xml_Parser_content___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_Parser_content___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_content(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_56; 
lean_inc(x_1);
x_56 = l_Lean_Xml_Parser_CharData(x_1);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_2 = x_57;
x_3 = x_60;
goto block_55;
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
x_64 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_62);
if (x_64 == 0)
{
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_65; 
lean_free_object(x_56);
lean_dec(x_63);
lean_dec(x_62);
x_65 = lean_box(0);
x_2 = x_1;
x_3 = x_65;
goto block_55;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_56, 0);
x_67 = lean_ctor_get(x_56, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_56);
x_68 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_1, x_66);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_1);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; 
lean_dec(x_67);
lean_dec(x_66);
x_70 = lean_box(0);
x_2 = x_1;
x_3 = x_70;
goto block_55;
}
}
}
block_55:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Xml_Parser_content___closed__1;
x_5 = l_Lean_Parsec_many(lean_box(0));
x_6 = lean_apply_2(x_5, x_4, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; size_t x_14; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Xml_Parser_content___closed__2;
x_10 = lean_array_push(x_9, x_3);
x_11 = lean_array_get_size(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = 0;
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_8);
x_15 = l_Lean_Xml_Parser_EmptyElemTag___closed__2;
x_16 = l_Array_append___rarg(x_10, x_15);
x_17 = lean_array_get_size(x_16);
x_18 = l_Array_filterMapM___at_Lean_Xml_Parser_content___spec__2(x_16, x_12, x_17);
lean_dec(x_16);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Xml_Parser_content___spec__4(x_18, x_20, x_14, x_15, x_7);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_11, x_11);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_8);
x_27 = l_Lean_Xml_Parser_EmptyElemTag___closed__2;
x_28 = l_Array_append___rarg(x_10, x_27);
x_29 = lean_array_get_size(x_28);
x_30 = l_Array_filterMapM___at_Lean_Xml_Parser_content___spec__2(x_28, x_12, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_30);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_33 = l_Array_forInUnsafe_loop___at_Lean_Xml_Parser_content___spec__4(x_30, x_32, x_14, x_27, x_7);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; lean_object* x_46; uint8_t x_47; 
x_38 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_39 = l_Lean_Xml_Parser_EmptyElemTag___closed__2;
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__5(x_8, x_14, x_38, x_39);
lean_dec(x_8);
x_41 = l_Array_append___rarg(x_10, x_40);
x_42 = lean_array_get_size(x_41);
x_43 = l_Array_filterMapM___at_Lean_Xml_Parser_content___spec__2(x_41, x_12, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_43);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = l_Array_forInUnsafe_loop___at_Lean_Xml_Parser_content___spec__4(x_43, x_45, x_14, x_39, x_7);
lean_dec(x_43);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
return x_6;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_6, 0);
x_53 = lean_ctor_get(x_6, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_6);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_element(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_elementPrefix(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_4);
x_5 = l_Lean_Xml_Parser_EmptyElemTag(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_11);
if (x_13 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_14; 
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_Lean_Xml_Parser_STag(x_4, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Xml_Parser_content(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_apply_1(x_16, x_19);
x_21 = l_Lean_Xml_Parser_ETag(x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 1);
lean_dec(x_23);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_16);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
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
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_5, 0);
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_5);
x_40 = l___private_Init_Data_String_Basic_0__String_decEqIterator____x40_Init_Data_String_Basic___hyg_1267_(x_3, x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_4);
lean_dec(x_3);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
x_42 = l_Lean_Xml_Parser_STag(x_4, x_3);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Xml_Parser_content(x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_1(x_44, x_47);
x_49 = l_Lean_Xml_Parser_ETag(x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_48);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_44);
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_59 = x_45;
} else {
 lean_dec_ref(x_45);
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
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_42, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_63 = x_42;
} else {
 lean_dec_ref(x_42);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_2);
if (x_65 == 0)
{
return x_2;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_2, 0);
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_2);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_back___at_Lean_Xml_Parser_content___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Xml_Parser_content___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Xml_Parser_content___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_Lean_Xml_Parser_content___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Xml_Parser_content___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Xml_Parser_content___spec__4(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Xml_Parser_content___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_Parser_document(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Xml_Parser_prolog(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Xml_Parser_element(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Xml_Parser_prolog___closed__1;
x_8 = l_Lean_Parsec_many(lean_box(0));
x_9 = lean_apply_2(x_8, x_7, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = l_String_Iterator_hasNext(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = l_Lean_Parsec_expectedEndOfInput;
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 1, x_14);
return x_9;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_String_Iterator_hasNext(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_18 = l_Lean_Parsec_expectedEndOfInput;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
return x_4;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Xml_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("offset ");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_parse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(": ");
return x_1;
}
}
static lean_object* _init_l_Lean_Xml_parse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Xml_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = l_Lean_Xml_Parser_document(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = l_Nat_repr(x_9);
x_11 = l_Lean_Xml_parse___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Xml_parse___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_8);
lean_dec(x_8);
x_16 = l_Lean_Xml_parse___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_unsigned_to_nat(10u);
lean_inc(x_7);
x_19 = l_String_Iterator_prevn(x_7, x_18);
x_20 = l_String_Iterator_extract(x_19, x_7);
lean_dec(x_7);
lean_dec(x_19);
x_21 = lean_string_append(x_17, x_20);
lean_dec(x_20);
x_22 = l_Lean_Xml_Parser_endl___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Parsec(lean_object*);
lean_object* initialize_Lean_Data_Xml_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Xml_Parser(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Parsec(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Xml_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Xml_Parser_endl___closed__1 = _init_l_Lean_Xml_Parser_endl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_endl___closed__1);
l_Lean_Xml_Parser_endl___closed__2 = _init_l_Lean_Xml_Parser_endl___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_endl___closed__2);
l_Lean_Xml_Parser_endl___closed__3 = _init_l_Lean_Xml_Parser_endl___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_endl___closed__3);
l_Lean_Xml_Parser_endl___closed__4 = _init_l_Lean_Xml_Parser_endl___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_endl___closed__4);
l_Lean_Xml_Parser_endl___closed__5 = _init_l_Lean_Xml_Parser_endl___closed__5();
lean_mark_persistent(l_Lean_Xml_Parser_endl___closed__5);
l_Lean_Xml_Parser_endl___closed__6 = _init_l_Lean_Xml_Parser_endl___closed__6();
lean_mark_persistent(l_Lean_Xml_Parser_endl___closed__6);
l_Lean_Xml_Parser_endl___closed__7 = _init_l_Lean_Xml_Parser_endl___closed__7();
lean_mark_persistent(l_Lean_Xml_Parser_endl___closed__7);
l_Lean_Xml_Parser_endl___closed__8 = _init_l_Lean_Xml_Parser_endl___closed__8();
lean_mark_persistent(l_Lean_Xml_Parser_endl___closed__8);
l_Lean_Xml_Parser_endl___closed__9 = _init_l_Lean_Xml_Parser_endl___closed__9();
lean_mark_persistent(l_Lean_Xml_Parser_endl___closed__9);
l_Lean_Xml_Parser_endl___closed__10 = _init_l_Lean_Xml_Parser_endl___closed__10();
lean_mark_persistent(l_Lean_Xml_Parser_endl___closed__10);
l_Lean_Xml_Parser_endl___boxed__const__1 = _init_l_Lean_Xml_Parser_endl___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_endl___boxed__const__1);
l_Lean_Xml_Parser_quote___rarg___closed__1 = _init_l_Lean_Xml_Parser_quote___rarg___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_quote___rarg___closed__1);
l_Lean_Xml_Parser_quote___rarg___closed__2 = _init_l_Lean_Xml_Parser_quote___rarg___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_quote___rarg___closed__2);
l_Lean_Xml_Parser_quote___rarg___closed__3 = _init_l_Lean_Xml_Parser_quote___rarg___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_quote___rarg___closed__3);
l_Lean_Xml_Parser_quote___rarg___closed__4 = _init_l_Lean_Xml_Parser_quote___rarg___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_quote___rarg___closed__4);
l_Lean_Xml_Parser_quote___rarg___closed__5 = _init_l_Lean_Xml_Parser_quote___rarg___closed__5();
lean_mark_persistent(l_Lean_Xml_Parser_quote___rarg___closed__5);
l_Lean_Xml_Parser_quote___rarg___closed__6 = _init_l_Lean_Xml_Parser_quote___rarg___closed__6();
lean_mark_persistent(l_Lean_Xml_Parser_quote___rarg___closed__6);
l_Lean_Xml_Parser_Char___closed__1 = _init_l_Lean_Xml_Parser_Char___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_Char___closed__1);
l_Lean_Xml_Parser_Char___closed__2 = _init_l_Lean_Xml_Parser_Char___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_Char___closed__2);
l_Lean_Xml_Parser_Char___closed__3 = _init_l_Lean_Xml_Parser_Char___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_Char___closed__3);
l_Lean_Xml_Parser_Char___closed__4 = _init_l_Lean_Xml_Parser_Char___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_Char___closed__4);
l_Lean_Xml_Parser_Char___boxed__const__1 = _init_l_Lean_Xml_Parser_Char___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_Char___boxed__const__1);
l_Lean_Xml_Parser_S___lambda__1___boxed__const__1 = _init_l_Lean_Xml_Parser_S___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_S___lambda__1___boxed__const__1);
l_Lean_Xml_Parser_S___closed__1___boxed__const__1 = _init_l_Lean_Xml_Parser_S___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_S___closed__1___boxed__const__1);
l_Lean_Xml_Parser_S___closed__1 = _init_l_Lean_Xml_Parser_S___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_S___closed__1);
l_Lean_Xml_Parser_Eq___closed__1 = _init_l_Lean_Xml_Parser_Eq___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_Eq___closed__1);
l_Lean_Xml_Parser_Eq___closed__2 = _init_l_Lean_Xml_Parser_Eq___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_Eq___closed__2);
l_Lean_Xml_Parser_Eq___closed__3 = _init_l_Lean_Xml_Parser_Eq___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_Eq___closed__3);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__1 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__1();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__1);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__2 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__2();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__2);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__3 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__3();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__3);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__4 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__4();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__4);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__5 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__5();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__5);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__6 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__6();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__6);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__7 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__7();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__7);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__8 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__8();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__8);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__9 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__9();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__9);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__10 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__10();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__10);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__11 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__11();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__11);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__12 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__12();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__12);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__13 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__13();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__13);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__14 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__14();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__14);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__15 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__15();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__15);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__16 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__16();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__16);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__17 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__17();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__17);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__18 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__18();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__18);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__19 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__19();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__19);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__20 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__20();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__20);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__21 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__21();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__21);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__22 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__22();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__22);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__23 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__23();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__23);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__24 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__24();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__24);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__25 = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__25();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges___closed__25);
l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges = _init_l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges();
lean_mark_persistent(l___private_Lean_Data_Xml_Parser_0__Lean_Xml_Parser_nameStartCharRanges);
l_Lean_Xml_Parser_NameStartChar___closed__1 = _init_l_Lean_Xml_Parser_NameStartChar___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_NameStartChar___closed__1);
l_Lean_Xml_Parser_NameStartChar___closed__2 = _init_l_Lean_Xml_Parser_NameStartChar___closed__2();
l_Lean_Xml_Parser_NameStartChar___closed__3 = _init_l_Lean_Xml_Parser_NameStartChar___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_NameStartChar___closed__3);
l_Lean_Xml_Parser_NameStartChar___closed__4 = _init_l_Lean_Xml_Parser_NameStartChar___closed__4();
l_Lean_Xml_Parser_NameStartChar___closed__5 = _init_l_Lean_Xml_Parser_NameStartChar___closed__5();
l_Lean_Xml_Parser_NameChar___closed__1 = _init_l_Lean_Xml_Parser_NameChar___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__1);
l_Lean_Xml_Parser_NameChar___closed__2 = _init_l_Lean_Xml_Parser_NameChar___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__2);
l_Lean_Xml_Parser_NameChar___closed__3 = _init_l_Lean_Xml_Parser_NameChar___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__3);
l_Lean_Xml_Parser_NameChar___closed__4 = _init_l_Lean_Xml_Parser_NameChar___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__4);
l_Lean_Xml_Parser_NameChar___closed__5 = _init_l_Lean_Xml_Parser_NameChar___closed__5();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__5);
l_Lean_Xml_Parser_NameChar___closed__6 = _init_l_Lean_Xml_Parser_NameChar___closed__6();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__6);
l_Lean_Xml_Parser_NameChar___closed__7 = _init_l_Lean_Xml_Parser_NameChar___closed__7();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__7);
l_Lean_Xml_Parser_NameChar___closed__8 = _init_l_Lean_Xml_Parser_NameChar___closed__8();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__8);
l_Lean_Xml_Parser_NameChar___closed__9 = _init_l_Lean_Xml_Parser_NameChar___closed__9();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__9);
l_Lean_Xml_Parser_NameChar___closed__10 = _init_l_Lean_Xml_Parser_NameChar___closed__10();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__10);
l_Lean_Xml_Parser_NameChar___closed__11 = _init_l_Lean_Xml_Parser_NameChar___closed__11();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___closed__11);
l_Lean_Xml_Parser_NameChar___boxed__const__1 = _init_l_Lean_Xml_Parser_NameChar___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___boxed__const__1);
l_Lean_Xml_Parser_NameChar___boxed__const__2 = _init_l_Lean_Xml_Parser_NameChar___boxed__const__2();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___boxed__const__2);
l_Lean_Xml_Parser_NameChar___boxed__const__3 = _init_l_Lean_Xml_Parser_NameChar___boxed__const__3();
lean_mark_persistent(l_Lean_Xml_Parser_NameChar___boxed__const__3);
l_Lean_Xml_Parser_Name___closed__1 = _init_l_Lean_Xml_Parser_Name___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_Name___closed__1);
l_Lean_Xml_Parser_VersionNum___closed__1 = _init_l_Lean_Xml_Parser_VersionNum___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_VersionNum___closed__1);
l_Lean_Xml_Parser_VersionNum___closed__2 = _init_l_Lean_Xml_Parser_VersionNum___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_VersionNum___closed__2);
l_Lean_Xml_Parser_VersionInfo___closed__1 = _init_l_Lean_Xml_Parser_VersionInfo___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_VersionInfo___closed__1);
l_Lean_Xml_Parser_VersionInfo___closed__2 = _init_l_Lean_Xml_Parser_VersionInfo___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_VersionInfo___closed__2);
l_Lean_Xml_Parser_EncName___lambda__1___closed__1 = _init_l_Lean_Xml_Parser_EncName___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_EncName___lambda__1___closed__1);
l_Lean_Xml_Parser_EncName___lambda__1___closed__2 = _init_l_Lean_Xml_Parser_EncName___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_EncName___lambda__1___closed__2);
l_Lean_Xml_Parser_EncName___lambda__1___closed__3 = _init_l_Lean_Xml_Parser_EncName___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_EncName___lambda__1___closed__3);
l_Lean_Xml_Parser_EncName___lambda__1___closed__4 = _init_l_Lean_Xml_Parser_EncName___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_EncName___lambda__1___closed__4);
l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__1 = _init_l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__1);
l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__2 = _init_l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__2();
lean_mark_persistent(l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__2);
l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__3 = _init_l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__3();
lean_mark_persistent(l_Lean_Xml_Parser_EncName___lambda__1___boxed__const__3);
l_Lean_Xml_Parser_EncName___closed__1 = _init_l_Lean_Xml_Parser_EncName___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_EncName___closed__1);
l_Lean_Xml_Parser_EncodingDecl___closed__1 = _init_l_Lean_Xml_Parser_EncodingDecl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_EncodingDecl___closed__1);
l_Lean_Xml_Parser_EncodingDecl___closed__2 = _init_l_Lean_Xml_Parser_EncodingDecl___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_EncodingDecl___closed__2);
l_Lean_Xml_Parser_SDDecl___lambda__1___closed__1 = _init_l_Lean_Xml_Parser_SDDecl___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_SDDecl___lambda__1___closed__1);
l_Lean_Xml_Parser_SDDecl___lambda__1___closed__2 = _init_l_Lean_Xml_Parser_SDDecl___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_SDDecl___lambda__1___closed__2);
l_Lean_Xml_Parser_SDDecl___closed__1 = _init_l_Lean_Xml_Parser_SDDecl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_SDDecl___closed__1);
l_Lean_Xml_Parser_SDDecl___closed__2 = _init_l_Lean_Xml_Parser_SDDecl___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_SDDecl___closed__2);
l_Lean_Xml_Parser_XMLdecl___closed__1 = _init_l_Lean_Xml_Parser_XMLdecl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_XMLdecl___closed__1);
l_Lean_Xml_Parser_XMLdecl___closed__2 = _init_l_Lean_Xml_Parser_XMLdecl___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_XMLdecl___closed__2);
l_Lean_Xml_Parser_Comment___closed__1 = _init_l_Lean_Xml_Parser_Comment___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_Comment___closed__1);
l_Lean_Xml_Parser_Comment___closed__2 = _init_l_Lean_Xml_Parser_Comment___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_Comment___closed__2);
l_Lean_Xml_Parser_Comment___closed__3 = _init_l_Lean_Xml_Parser_Comment___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_Comment___closed__3);
l_Lean_Xml_Parser_PITarget___closed__1 = _init_l_Lean_Xml_Parser_PITarget___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__1);
l_Lean_Xml_Parser_PITarget___closed__2 = _init_l_Lean_Xml_Parser_PITarget___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__2);
l_Lean_Xml_Parser_PITarget___closed__3 = _init_l_Lean_Xml_Parser_PITarget___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__3);
l_Lean_Xml_Parser_PITarget___closed__4 = _init_l_Lean_Xml_Parser_PITarget___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__4);
l_Lean_Xml_Parser_PITarget___closed__5 = _init_l_Lean_Xml_Parser_PITarget___closed__5();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__5);
l_Lean_Xml_Parser_PITarget___closed__6 = _init_l_Lean_Xml_Parser_PITarget___closed__6();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__6);
l_Lean_Xml_Parser_PITarget___closed__7 = _init_l_Lean_Xml_Parser_PITarget___closed__7();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__7);
l_Lean_Xml_Parser_PITarget___closed__8 = _init_l_Lean_Xml_Parser_PITarget___closed__8();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__8);
l_Lean_Xml_Parser_PITarget___closed__9 = _init_l_Lean_Xml_Parser_PITarget___closed__9();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__9);
l_Lean_Xml_Parser_PITarget___closed__10 = _init_l_Lean_Xml_Parser_PITarget___closed__10();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__10);
l_Lean_Xml_Parser_PITarget___closed__11 = _init_l_Lean_Xml_Parser_PITarget___closed__11();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__11);
l_Lean_Xml_Parser_PITarget___closed__12 = _init_l_Lean_Xml_Parser_PITarget___closed__12();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__12);
l_Lean_Xml_Parser_PITarget___closed__13 = _init_l_Lean_Xml_Parser_PITarget___closed__13();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__13);
l_Lean_Xml_Parser_PITarget___closed__14 = _init_l_Lean_Xml_Parser_PITarget___closed__14();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__14);
l_Lean_Xml_Parser_PITarget___closed__15 = _init_l_Lean_Xml_Parser_PITarget___closed__15();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__15);
l_Lean_Xml_Parser_PITarget___closed__16 = _init_l_Lean_Xml_Parser_PITarget___closed__16();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__16);
l_Lean_Xml_Parser_PITarget___closed__17 = _init_l_Lean_Xml_Parser_PITarget___closed__17();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__17);
l_Lean_Xml_Parser_PITarget___closed__18 = _init_l_Lean_Xml_Parser_PITarget___closed__18();
lean_mark_persistent(l_Lean_Xml_Parser_PITarget___closed__18);
l_Lean_Xml_Parser_PI___closed__1 = _init_l_Lean_Xml_Parser_PI___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_PI___closed__1);
l_Lean_Xml_Parser_PI___closed__2 = _init_l_Lean_Xml_Parser_PI___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_PI___closed__2);
l_Lean_Xml_Parser_SystemLiteral___closed__1___boxed__const__1 = _init_l_Lean_Xml_Parser_SystemLiteral___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_SystemLiteral___closed__1___boxed__const__1);
l_Lean_Xml_Parser_SystemLiteral___closed__1 = _init_l_Lean_Xml_Parser_SystemLiteral___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_SystemLiteral___closed__1);
l_Lean_Xml_Parser_SystemLiteral___closed__2 = _init_l_Lean_Xml_Parser_SystemLiteral___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_SystemLiteral___closed__2);
l_Lean_Xml_Parser_SystemLiteral___closed__3___boxed__const__1 = _init_l_Lean_Xml_Parser_SystemLiteral___closed__3___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_SystemLiteral___closed__3___boxed__const__1);
l_Lean_Xml_Parser_SystemLiteral___closed__3 = _init_l_Lean_Xml_Parser_SystemLiteral___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_SystemLiteral___closed__3);
l_Lean_Xml_Parser_SystemLiteral___closed__4 = _init_l_Lean_Xml_Parser_SystemLiteral___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_SystemLiteral___closed__4);
l_Lean_Xml_Parser_PubidChar___closed__1 = _init_l_Lean_Xml_Parser_PubidChar___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_PubidChar___closed__1);
l_Lean_Xml_Parser_PubidChar___closed__2 = _init_l_Lean_Xml_Parser_PubidChar___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_PubidChar___closed__2);
l_Lean_Xml_Parser_PubidLiteral___lambda__1___closed__1 = _init_l_Lean_Xml_Parser_PubidLiteral___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_PubidLiteral___lambda__1___closed__1);
l_Lean_Xml_Parser_PubidLiteral___closed__1___boxed__const__1 = _init_l_Lean_Xml_Parser_PubidLiteral___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_PubidLiteral___closed__1___boxed__const__1);
l_Lean_Xml_Parser_PubidLiteral___closed__1 = _init_l_Lean_Xml_Parser_PubidLiteral___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_PubidLiteral___closed__1);
l_Lean_Xml_Parser_PubidLiteral___closed__2 = _init_l_Lean_Xml_Parser_PubidLiteral___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_PubidLiteral___closed__2);
l_Lean_Xml_Parser_PubidLiteral___closed__3 = _init_l_Lean_Xml_Parser_PubidLiteral___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_PubidLiteral___closed__3);
l_Lean_Xml_Parser_ExternalID___closed__1 = _init_l_Lean_Xml_Parser_ExternalID___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_ExternalID___closed__1);
l_Lean_Xml_Parser_ExternalID___closed__2 = _init_l_Lean_Xml_Parser_ExternalID___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_ExternalID___closed__2);
l_Lean_Xml_Parser_Mixed___lambda__1___closed__1 = _init_l_Lean_Xml_Parser_Mixed___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___lambda__1___closed__1);
l_Lean_Xml_Parser_Mixed___lambda__1___closed__2 = _init_l_Lean_Xml_Parser_Mixed___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___lambda__1___closed__2);
l_Lean_Xml_Parser_Mixed___lambda__1___closed__3 = _init_l_Lean_Xml_Parser_Mixed___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___lambda__1___closed__3);
l_Lean_Xml_Parser_Mixed___closed__1 = _init_l_Lean_Xml_Parser_Mixed___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___closed__1);
l_Lean_Xml_Parser_Mixed___closed__2 = _init_l_Lean_Xml_Parser_Mixed___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___closed__2);
l_Lean_Xml_Parser_Mixed___closed__3 = _init_l_Lean_Xml_Parser_Mixed___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___closed__3);
l_Lean_Xml_Parser_Mixed___closed__4 = _init_l_Lean_Xml_Parser_Mixed___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___closed__4);
l_Lean_Xml_Parser_Mixed___closed__5 = _init_l_Lean_Xml_Parser_Mixed___closed__5();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___closed__5);
l_Lean_Xml_Parser_Mixed___closed__6 = _init_l_Lean_Xml_Parser_Mixed___closed__6();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___closed__6);
l_Lean_Xml_Parser_Mixed___closed__7 = _init_l_Lean_Xml_Parser_Mixed___closed__7();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___closed__7);
l_Lean_Xml_Parser_Mixed___closed__8 = _init_l_Lean_Xml_Parser_Mixed___closed__8();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___closed__8);
l_Lean_Xml_Parser_Mixed___closed__9 = _init_l_Lean_Xml_Parser_Mixed___closed__9();
lean_mark_persistent(l_Lean_Xml_Parser_Mixed___closed__9);
l_Lean_Xml_Parser_cp___closed__1 = _init_l_Lean_Xml_Parser_cp___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_cp___closed__1);
l_Lean_Xml_Parser_cp___closed__2 = _init_l_Lean_Xml_Parser_cp___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_cp___closed__2);
l_Lean_Xml_Parser_cp___closed__3 = _init_l_Lean_Xml_Parser_cp___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_cp___closed__3);
l_Lean_Xml_Parser_cp___closed__4 = _init_l_Lean_Xml_Parser_cp___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_cp___closed__4);
l_Lean_Xml_Parser_cp___closed__5 = _init_l_Lean_Xml_Parser_cp___closed__5();
lean_mark_persistent(l_Lean_Xml_Parser_cp___closed__5);
l_Lean_Xml_Parser_cp___closed__6 = _init_l_Lean_Xml_Parser_cp___closed__6();
lean_mark_persistent(l_Lean_Xml_Parser_cp___closed__6);
l_Lean_Xml_Parser_cp___closed__7 = _init_l_Lean_Xml_Parser_cp___closed__7();
lean_mark_persistent(l_Lean_Xml_Parser_cp___closed__7);
l_Lean_Xml_Parser_cp___closed__8 = _init_l_Lean_Xml_Parser_cp___closed__8();
lean_mark_persistent(l_Lean_Xml_Parser_cp___closed__8);
l_Lean_Xml_Parser_cp___closed__9 = _init_l_Lean_Xml_Parser_cp___closed__9();
lean_mark_persistent(l_Lean_Xml_Parser_cp___closed__9);
l_Lean_Xml_Parser_seq___lambda__1___closed__1 = _init_l_Lean_Xml_Parser_seq___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_seq___lambda__1___closed__1);
l_Lean_Xml_Parser_seq___lambda__1___closed__2 = _init_l_Lean_Xml_Parser_seq___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_seq___lambda__1___closed__2);
l_Lean_Xml_Parser_seq___lambda__1___closed__3 = _init_l_Lean_Xml_Parser_seq___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_seq___lambda__1___closed__3);
l_Lean_Xml_Parser_seq___closed__1 = _init_l_Lean_Xml_Parser_seq___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_seq___closed__1);
l_Lean_Xml_Parser_choice___closed__1 = _init_l_Lean_Xml_Parser_choice___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_choice___closed__1);
l_Lean_Xml_Parser_contentspec___closed__1 = _init_l_Lean_Xml_Parser_contentspec___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_contentspec___closed__1);
l_Lean_Xml_Parser_contentspec___closed__2 = _init_l_Lean_Xml_Parser_contentspec___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_contentspec___closed__2);
l_Lean_Xml_Parser_elementDecl___closed__1 = _init_l_Lean_Xml_Parser_elementDecl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_elementDecl___closed__1);
l_Lean_Xml_Parser_elementDecl___closed__2 = _init_l_Lean_Xml_Parser_elementDecl___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_elementDecl___closed__2);
l_Lean_Xml_Parser_elementDecl___closed__3 = _init_l_Lean_Xml_Parser_elementDecl___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_elementDecl___closed__3);
l_Lean_Xml_Parser_elementDecl___closed__4 = _init_l_Lean_Xml_Parser_elementDecl___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_elementDecl___closed__4);
l_Lean_Xml_Parser_StringType___closed__1 = _init_l_Lean_Xml_Parser_StringType___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_StringType___closed__1);
l_Lean_Xml_Parser_TokenizedType___closed__1 = _init_l_Lean_Xml_Parser_TokenizedType___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_TokenizedType___closed__1);
l_Lean_Xml_Parser_TokenizedType___closed__2 = _init_l_Lean_Xml_Parser_TokenizedType___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_TokenizedType___closed__2);
l_Lean_Xml_Parser_TokenizedType___closed__3 = _init_l_Lean_Xml_Parser_TokenizedType___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_TokenizedType___closed__3);
l_Lean_Xml_Parser_TokenizedType___closed__4 = _init_l_Lean_Xml_Parser_TokenizedType___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_TokenizedType___closed__4);
l_Lean_Xml_Parser_TokenizedType___closed__5 = _init_l_Lean_Xml_Parser_TokenizedType___closed__5();
lean_mark_persistent(l_Lean_Xml_Parser_TokenizedType___closed__5);
l_Lean_Xml_Parser_TokenizedType___closed__6 = _init_l_Lean_Xml_Parser_TokenizedType___closed__6();
lean_mark_persistent(l_Lean_Xml_Parser_TokenizedType___closed__6);
l_Lean_Xml_Parser_TokenizedType___closed__7 = _init_l_Lean_Xml_Parser_TokenizedType___closed__7();
lean_mark_persistent(l_Lean_Xml_Parser_TokenizedType___closed__7);
l_Lean_Xml_Parser_NotationType___closed__1 = _init_l_Lean_Xml_Parser_NotationType___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_NotationType___closed__1);
l_Lean_Xml_Parser_Enumeration___closed__1 = _init_l_Lean_Xml_Parser_Enumeration___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_Enumeration___closed__1);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__1 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__1);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__2 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__2);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__3 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__3);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__4 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__4);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__5 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__5();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__5);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__6___boxed__const__1 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__6___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__6___boxed__const__1);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__6 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__6();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__6);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__7___boxed__const__1 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__7___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__7___boxed__const__1);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__7 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__7();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__7);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__8___boxed__const__1 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__8___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__8___boxed__const__1);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__8 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__8();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__8);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__9___boxed__const__1 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__9___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__9___boxed__const__1);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__9 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__9();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__9);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__10___boxed__const__1 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__10___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__10___boxed__const__1);
l_Lean_Xml_Parser_predefinedEntityToChar___closed__10 = _init_l_Lean_Xml_Parser_predefinedEntityToChar___closed__10();
lean_mark_persistent(l_Lean_Xml_Parser_predefinedEntityToChar___closed__10);
l_Lean_Xml_Parser_EntityRef___closed__1 = _init_l_Lean_Xml_Parser_EntityRef___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_EntityRef___closed__1);
l_Lean_Xml_Parser_EntityRef___closed__2 = _init_l_Lean_Xml_Parser_EntityRef___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_EntityRef___closed__2);
l_Lean_Xml_Parser_EntityRef___closed__3 = _init_l_Lean_Xml_Parser_EntityRef___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_EntityRef___closed__3);
l_Lean_Xml_Parser_EntityRef___closed__4 = _init_l_Lean_Xml_Parser_EntityRef___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_EntityRef___closed__4);
l_Lean_Xml_Parser_EntityRef___closed__5 = _init_l_Lean_Xml_Parser_EntityRef___closed__5();
lean_mark_persistent(l_Lean_Xml_Parser_EntityRef___closed__5);
l_Lean_Xml_Parser_EntityRef___closed__6 = _init_l_Lean_Xml_Parser_EntityRef___closed__6();
lean_mark_persistent(l_Lean_Xml_Parser_EntityRef___closed__6);
l_Lean_Xml_Parser_CharRef___lambda__2___closed__1 = _init_l_Lean_Xml_Parser_CharRef___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_CharRef___lambda__2___closed__1);
l_Lean_Xml_Parser_CharRef___closed__1 = _init_l_Lean_Xml_Parser_CharRef___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_CharRef___closed__1);
l_Lean_Xml_Parser_CharRef___closed__2 = _init_l_Lean_Xml_Parser_CharRef___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_CharRef___closed__2);
l_Lean_Xml_Parser_CharRef___closed__3 = _init_l_Lean_Xml_Parser_CharRef___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_CharRef___closed__3);
l_Lean_Xml_Parser_AttValue___closed__1___boxed__const__1 = _init_l_Lean_Xml_Parser_AttValue___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_AttValue___closed__1___boxed__const__1);
l_Lean_Xml_Parser_AttValue___closed__1 = _init_l_Lean_Xml_Parser_AttValue___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_AttValue___closed__1);
l_Lean_Xml_Parser_AttValue___closed__2___boxed__const__1 = _init_l_Lean_Xml_Parser_AttValue___closed__2___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_AttValue___closed__2___boxed__const__1);
l_Lean_Xml_Parser_AttValue___closed__2 = _init_l_Lean_Xml_Parser_AttValue___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_AttValue___closed__2);
l_Lean_Xml_Parser_DefaultDecl___closed__1 = _init_l_Lean_Xml_Parser_DefaultDecl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_DefaultDecl___closed__1);
l_Lean_Xml_Parser_DefaultDecl___closed__2 = _init_l_Lean_Xml_Parser_DefaultDecl___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_DefaultDecl___closed__2);
l_Lean_Xml_Parser_DefaultDecl___closed__3 = _init_l_Lean_Xml_Parser_DefaultDecl___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_DefaultDecl___closed__3);
l_Lean_Xml_Parser_AttlistDecl___closed__1 = _init_l_Lean_Xml_Parser_AttlistDecl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_AttlistDecl___closed__1);
l_Lean_Xml_Parser_AttlistDecl___closed__2 = _init_l_Lean_Xml_Parser_AttlistDecl___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_AttlistDecl___closed__2);
l_Lean_Xml_Parser_PEReference___closed__1 = _init_l_Lean_Xml_Parser_PEReference___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_PEReference___closed__1);
l_Lean_Xml_Parser_PEReference___closed__2 = _init_l_Lean_Xml_Parser_PEReference___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_PEReference___closed__2);
l_Lean_Xml_Parser_PEReference___closed__3 = _init_l_Lean_Xml_Parser_PEReference___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_PEReference___closed__3);
l_Lean_Xml_Parser_EntityValue___closed__1___boxed__const__1 = _init_l_Lean_Xml_Parser_EntityValue___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_EntityValue___closed__1___boxed__const__1);
l_Lean_Xml_Parser_EntityValue___closed__1 = _init_l_Lean_Xml_Parser_EntityValue___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_EntityValue___closed__1);
l_Lean_Xml_Parser_EntityValue___closed__2___boxed__const__1 = _init_l_Lean_Xml_Parser_EntityValue___closed__2___boxed__const__1();
lean_mark_persistent(l_Lean_Xml_Parser_EntityValue___closed__2___boxed__const__1);
l_Lean_Xml_Parser_EntityValue___closed__2 = _init_l_Lean_Xml_Parser_EntityValue___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_EntityValue___closed__2);
l_Lean_Xml_Parser_NDataDecl___closed__1 = _init_l_Lean_Xml_Parser_NDataDecl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_NDataDecl___closed__1);
l_Lean_Xml_Parser_GEDecl___closed__1 = _init_l_Lean_Xml_Parser_GEDecl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_GEDecl___closed__1);
l_Lean_Xml_Parser_NotationDecl___closed__1 = _init_l_Lean_Xml_Parser_NotationDecl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_NotationDecl___closed__1);
l_Lean_Xml_Parser_intSubset___closed__1 = _init_l_Lean_Xml_Parser_intSubset___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_intSubset___closed__1);
l_Lean_Xml_Parser_doctypedecl___closed__1 = _init_l_Lean_Xml_Parser_doctypedecl___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_doctypedecl___closed__1);
l_Lean_Xml_Parser_doctypedecl___closed__2 = _init_l_Lean_Xml_Parser_doctypedecl___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_doctypedecl___closed__2);
l_Lean_Xml_Parser_doctypedecl___closed__3 = _init_l_Lean_Xml_Parser_doctypedecl___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_doctypedecl___closed__3);
l_Lean_Xml_Parser_doctypedecl___closed__4 = _init_l_Lean_Xml_Parser_doctypedecl___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_doctypedecl___closed__4);
l_Lean_Xml_Parser_doctypedecl___closed__5 = _init_l_Lean_Xml_Parser_doctypedecl___closed__5();
lean_mark_persistent(l_Lean_Xml_Parser_doctypedecl___closed__5);
l_Lean_Xml_Parser_doctypedecl___closed__6 = _init_l_Lean_Xml_Parser_doctypedecl___closed__6();
lean_mark_persistent(l_Lean_Xml_Parser_doctypedecl___closed__6);
l_Lean_Xml_Parser_doctypedecl___closed__7 = _init_l_Lean_Xml_Parser_doctypedecl___closed__7();
lean_mark_persistent(l_Lean_Xml_Parser_doctypedecl___closed__7);
l_Lean_Xml_Parser_prolog___closed__1 = _init_l_Lean_Xml_Parser_prolog___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_prolog___closed__1);
l_Lean_Xml_Parser_elementPrefix___closed__1 = _init_l_Lean_Xml_Parser_elementPrefix___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_elementPrefix___closed__1);
l_Lean_Xml_Parser_elementPrefix___closed__2 = _init_l_Lean_Xml_Parser_elementPrefix___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_elementPrefix___closed__2);
l_Lean_Xml_Parser_elementPrefix___closed__3 = _init_l_Lean_Xml_Parser_elementPrefix___closed__3();
lean_mark_persistent(l_Lean_Xml_Parser_elementPrefix___closed__3);
l_Lean_Xml_Parser_elementPrefix___closed__4 = _init_l_Lean_Xml_Parser_elementPrefix___closed__4();
lean_mark_persistent(l_Lean_Xml_Parser_elementPrefix___closed__4);
l_Lean_Xml_Parser_EmptyElemTag___closed__1 = _init_l_Lean_Xml_Parser_EmptyElemTag___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_EmptyElemTag___closed__1);
l_Lean_Xml_Parser_EmptyElemTag___closed__2 = _init_l_Lean_Xml_Parser_EmptyElemTag___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_EmptyElemTag___closed__2);
l_Lean_Xml_Parser_ETag___closed__1 = _init_l_Lean_Xml_Parser_ETag___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_ETag___closed__1);
l_Lean_Xml_Parser_CDStart___closed__1 = _init_l_Lean_Xml_Parser_CDStart___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_CDStart___closed__1);
l_Lean_Xml_Parser_CDEnd___closed__1 = _init_l_Lean_Xml_Parser_CDEnd___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_CDEnd___closed__1);
l_Lean_Xml_Parser_CData___closed__1 = _init_l_Lean_Xml_Parser_CData___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_CData___closed__1);
l_Lean_Xml_Parser_CharData___closed__1 = _init_l_Lean_Xml_Parser_CharData___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_CharData___closed__1);
l_Lean_Xml_Parser_CharData___closed__2 = _init_l_Lean_Xml_Parser_CharData___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_CharData___closed__2);
l_Lean_Xml_Parser_content___lambda__1___closed__1 = _init_l_Lean_Xml_Parser_content___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_content___lambda__1___closed__1);
l_Lean_Xml_Parser_content___closed__1 = _init_l_Lean_Xml_Parser_content___closed__1();
lean_mark_persistent(l_Lean_Xml_Parser_content___closed__1);
l_Lean_Xml_Parser_content___closed__2 = _init_l_Lean_Xml_Parser_content___closed__2();
lean_mark_persistent(l_Lean_Xml_Parser_content___closed__2);
l_Lean_Xml_parse___closed__1 = _init_l_Lean_Xml_parse___closed__1();
lean_mark_persistent(l_Lean_Xml_parse___closed__1);
l_Lean_Xml_parse___closed__2 = _init_l_Lean_Xml_parse___closed__2();
lean_mark_persistent(l_Lean_Xml_parse___closed__2);
l_Lean_Xml_parse___closed__3 = _init_l_Lean_Xml_parse___closed__3();
lean_mark_persistent(l_Lean_Xml_parse___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
