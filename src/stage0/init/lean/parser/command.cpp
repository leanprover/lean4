// Lean compiler output
// Module: init.lean.parser.command
// Imports: init.lean.parser.term
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_Lean_Parser_Command_visibility___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Command_declModifiers___closed__3;
extern obj* l_Lean_Parser_Term_id___closed__2;
obj* l_Lean_Parser_Command_attrInstance___elambda__1___closed__2;
obj* l_Lean_Parser_Command_noncomputable___closed__4;
obj* l_Lean_Parser_Command_protected___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_Command_declId___closed__7;
obj* l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Command_docComment___closed__2;
extern obj* l_Lean_Parser_Term_id___elambda__1___closed__9;
obj* l_Lean_Parser_Command_declModifiers;
obj* l_Lean_Parser_Command_def___closed__5;
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_declId___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_protected___elambda__1(obj*);
obj* l_Lean_Parser_Command_noncomputable___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Command_declId___elambda__1___closed__2;
extern obj* l_Lean_Parser_Term_optType;
extern obj* l_Lean_Parser_Term_id___elambda__1___closed__6;
obj* l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Command_visibility___closed__2;
obj* l_Lean_Parser_Command_attributes___elambda__1___closed__6;
obj* l_Lean_FileMap_toPosition___main(obj*, obj*);
obj* l_Lean_Parser_Command_commentBody___elambda__1(obj*);
obj* l_Lean_Parser_Command_def___elambda__1___closed__2;
obj* l_Lean_Parser_commandParserFn___boxed(obj*);
obj* l_Lean_Parser_builtinCommandParsingTable;
obj* l_Lean_Parser_ParserState_restore(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_attributes___elambda__1___closed__1;
obj* l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__4;
obj* l_Lean_Parser_commandParser___elambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_commentBody___elambda__1___boxed(obj*);
obj* l_Lean_Parser_regBuiltinCommandParserAttr___closed__1;
obj* l_Lean_Parser_Command_attrArg___closed__4;
extern obj* l_Lean_Parser_Term_list___closed__4;
obj* l_Lean_Parser_symbolInfo(obj*, obj*);
obj* l_Lean_Parser_Command_declValSimple___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Command_declValEqns___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declModifiers___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_attrArg___elambda__1___boxed(obj*);
obj* l_Lean_Parser_andthenInfo(obj*, obj*);
extern obj* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
obj* l_Lean_Parser_orelseInfo(obj*, obj*);
obj* l_Lean_Parser_Command_def___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_def___closed__2;
obj* l_Lean_Parser_Command_declSig;
obj* l_Lean_Parser_Command_protected___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Command_noncomputable___closed__2;
obj* l_Lean_Parser_Command_attributes___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declModifiers___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declSig___closed__4;
obj* l_Lean_Parser_Command_declSig___elambda__1___closed__1;
obj* l_Lean_Parser_Command_declVal___closed__1;
obj* l_Lean_Parser_Command_commentBody;
obj* l_Lean_Parser_Command_unsafe___elambda__1(obj*);
obj* l_Lean_Parser_Command_declId___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declId___closed__5;
obj* l_Lean_Parser_Command_private___closed__2;
obj* l_Lean_Parser_sepBy1Info(obj*, obj*);
obj* l_Lean_Parser_Command_visibility;
extern obj* l_Lean_Parser_builtinTermParsingTable;
obj* l_Lean_Parser_Command_protected;
obj* l_Lean_Parser_Command_attributes___elambda__1___closed__2;
obj* l_Lean_Parser_Command_theorem___closed__7;
obj* l_Lean_Parser_Command_declId___closed__1;
obj* l_Lean_Parser_Command_declModifiers___closed__10;
obj* l_Lean_Parser_Command_declValSimple___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_regBuiltinCommandParserAttr___closed__3;
obj* l_Lean_Parser_Command_declValEqns___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_attrArg___closed__3;
obj* l_Lean_Parser_Command_private___closed__4;
extern obj* l_Lean_Parser_Term_id___elambda__1___closed__11;
obj* l_Lean_Parser_Command_declId___closed__2;
obj* l_Lean_Parser_Command_docComment___closed__4;
obj* l_Lean_Parser_Command_declValSimple___elambda__1(obj*);
obj* l_Lean_Parser_Command_declValSimple;
obj* l_Lean_Parser_Command_commentBody___closed__2;
obj* l_Lean_Parser_Command_optDeclSig;
obj* l_Lean_Parser_Command_declVal___closed__3;
obj* l_Lean_Parser_symbolFnAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declId___closed__6;
obj* l_Lean_Parser_Command_declModifiers___closed__7;
obj* l_Lean_Parser_registerBuiltinParserAttribute(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_docComment___closed__1;
obj* l_Lean_Parser_Command_theorem___closed__5;
obj* l_Lean_Parser_Command_optDeclSig___closed__4;
extern obj* l_Lean_Parser_symbolFn___rarg___closed__1;
obj* l_Lean_Parser_Command_attributes___elambda__1___closed__5;
obj* l_Lean_Parser_Command_theorem___elambda__1___closed__1;
extern obj* l_Lean_Parser_termParserFn___rarg___closed__1;
obj* l_Lean_Parser_Command_private___closed__3;
obj* l_Lean_Parser_Command_declSig___closed__1;
obj* l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Command_attributes___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__4;
obj* l_Lean_Parser_Command_commentBody___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__2(obj*, uint8, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Command_attrInstance___closed__4;
obj* l_Lean_Parser_Command_declModifiers___elambda__1___closed__2;
extern obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_letEqns___elambda__1___spec__1___closed__1;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Command_theorem___closed__4;
obj* l_Lean_Parser_Command_attrArg___elambda__1(obj*);
obj* l_Lean_Parser_Command_attributes___closed__6;
obj* l_Lean_Parser_Command_noncomputable___closed__1;
obj* l_Lean_Parser_Command_theorem___closed__2;
obj* l_Lean_Parser_Command_declId___closed__8;
extern obj* l_Lean_Parser_Term_list___elambda__1___closed__4;
obj* l_Lean_Parser_Command_declModifiers___closed__1;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_theorem___elambda__1___closed__3;
obj* l_Lean_Parser_Command_theorem___closed__6;
obj* l_Lean_Parser_Command_visibility___elambda__1(obj*);
obj* l_Lean_Parser_Command_docComment;
obj* l_Lean_Parser_Command_protected___closed__3;
obj* l_Lean_Parser_ParserState_mkNode(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declValSimple___closed__1;
obj* l_Lean_Parser_Command_attrInstance___closed__2;
obj* l_Lean_Parser_Command_attributes___closed__5;
obj* l_Lean_Parser_Command_attrInstance___closed__3;
obj* l_Lean_Parser_Command_unsafe___closed__1;
obj* l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__7;
obj* l_Lean_Parser_Command_theorem___elambda__1___closed__2;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_def___elambda__1___closed__1;
obj* l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__1;
extern obj* l_Lean_Parser_manyAux___main___closed__1;
obj* l_Lean_Parser_runBuiltinParserUnsafe(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_theorem;
extern obj* l_Lean_Parser_Parser_inhabited___closed__1;
obj* l_Lean_Parser_Command_theorem___closed__3;
obj* l_Lean_Parser_Command_protected___closed__1;
obj* l_Lean_Parser_Command_attrInstance;
obj* l_Lean_Parser_Command_theorem___elambda__1___closed__6;
obj* l_Lean_Parser_Command_attributes___elambda__1___closed__3;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_manyAux___main(uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_docComment___closed__3;
obj* l_Lean_Parser_Term_typeSpec___elambda__1___rarg(obj*, obj*);
extern obj* l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_Command_declValEqns___closed__3;
obj* l_Lean_Parser_Command_protected___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Command_def___closed__3;
extern obj* l_Lean_Parser_Term_letEqns___closed__2;
obj* l_Lean_Parser_Command_private___elambda__1___rarg(obj*, obj*);
extern obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1___closed__1;
obj* l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
obj* l_Lean_Parser_Command_def___closed__7;
obj* l_Lean_Parser_Command_declModifiers___closed__9;
obj* l_Lean_Parser_Command_declVal___closed__2;
obj* l_Lean_Parser_Command_unsafe___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_commandParserFn___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declModifiers___closed__5;
obj* l_Lean_Parser_Command_attrInstance___elambda__1___closed__1;
extern obj* l_Lean_Parser_Term_id___closed__4;
extern obj* l_Char_HasRepr___closed__1;
extern obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2___closed__3;
obj* l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_Command_private___elambda__1___boxed(obj*);
extern obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2___closed__1;
obj* l_Lean_Parser_regBuiltinCommandParserAttr(obj*);
obj* l_Lean_Parser_Command_private___elambda__1___rarg___closed__4;
obj* l_Lean_Parser_Command_protected___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Command_theorem___elambda__1___closed__5;
obj* l_Lean_Parser_Command_declModifiers___closed__12;
obj* l_Lean_Parser_Command_declId___closed__4;
obj* l_Lean_Parser_Command_private___elambda__1(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_Command_declModifiers___closed__11;
obj* l_Lean_Parser_commandParser___elambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_commentBody___closed__1;
extern obj* l_Lean_nullKind;
obj* l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_strLitFn___rarg(obj*, obj*);
obj* l_Lean_Parser_Command_attrArg___closed__2;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Command_declValEqns;
obj* l_Lean_Parser_Command_def___elambda__1___closed__3;
obj* l_Lean_Parser_Command_visibility___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Command_theorem___closed__1;
obj* l_Lean_Parser_Command_attrInstance___closed__5;
obj* l_Lean_Parser_regBuiltinCommandParserAttr___closed__2;
obj* l_Lean_Parser_Command_unsafe;
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_attributes___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Command_declId___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declValEqns___closed__1;
obj* l_Lean_Parser_Command_declModifiers___closed__2;
obj* l_Lean_Parser_Term_equation___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_def___elambda__1___closed__6;
extern obj* l_Lean_Parser_Term_haveAssign___closed__3;
obj* l_Lean_Parser_Command_docComment___elambda__1(obj*);
obj* l_Lean_Parser_Command_visibility___closed__3;
obj* l_Lean_Parser_Command_noncomputable___elambda__1(obj*);
obj* l_Lean_Parser_Command_unsafe___closed__2;
obj* l_Lean_Parser_finishCommentBlock___main(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_theorem___elambda__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_attributes___elambda__1___spec__2(uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_numLitFn___rarg(obj*, obj*);
obj* l_Lean_Parser_Command_docComment___elambda__1___boxed(obj*);
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_attributes___elambda__1___spec__1(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_attrInstance___closed__1;
obj* l_Lean_Parser_noFirstTokenInfo(obj*);
obj* l_Lean_Parser_ParserState_pushSyntax(obj*, obj*);
obj* l_Lean_Parser_commandParser(obj*);
obj* l_Lean_Parser_Command_declSig___elambda__1___closed__2;
obj* l_Lean_Parser_Command_private___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Command_declValEqns___elambda__1___closed__1;
obj* l_Lean_Parser_Command_def___elambda__1___closed__4;
extern obj* l_Lean_Parser_Term_id___elambda__1___closed__7;
obj* l_Lean_Parser_Command_unsafe___closed__3;
extern obj* l_Lean_Parser_numLit___closed__1;
obj* l_Lean_Parser_identFn___rarg(obj*, obj*);
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___spec__2(obj*, uint8, obj*, obj*, obj*);
obj* l_String_trim(obj*);
extern obj* l_Lean_Parser_ident___closed__2;
obj* l_Lean_Parser_Command_declVal___elambda__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_declId___elambda__1___spec__2(uint8, uint8, obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_commandParserFn___rarg___closed__1;
obj* l_Lean_Parser_Command_declVal;
obj* l_Lean_Parser_Command_declVal___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_attrArg___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Command_optDeclSig___closed__2;
obj* l_Lean_Parser_Command_private___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Command_attributes___closed__1;
obj* l_Lean_Parser_Command_declModifiers___closed__4;
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Command_attributes___spec__1(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declValSimple___closed__2;
obj* l_Lean_Parser_Command_unsafe___closed__4;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_declId___elambda__1___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declModifiers___closed__6;
obj* l_Lean_Parser_Command_optDeclSig___closed__3;
obj* l_Lean_Parser_Command_def;
obj* l_Lean_Parser_Command_declId;
obj* l_Lean_Parser_Command_attributes___closed__7;
obj* l_Lean_Parser_ParserState_mkError(obj*, obj*);
obj* l_Lean_Parser_nodeInfo(obj*);
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Command_declId___spec__1(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declSig___closed__3;
obj* l_Array_size(obj*, obj*);
obj* l_Lean_Parser_Command_private___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_Command_declModifiers___elambda__1___closed__1;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___spec__1(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declSig___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_declId___elambda__1___spec__1(uint8, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declValEqns___closed__2;
obj* l_Lean_Parser_Command_def___closed__1;
extern obj* l_Lean_Parser_strLit___closed__1;
obj* l_Lean_Parser_Command_optDeclSig___elambda__1___closed__2;
obj* l_Lean_Parser_Command_visibility___closed__1;
obj* l_Lean_Parser_commandParserFn___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_attrInstance___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_unsafe___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Command_attributes___elambda__1___closed__4;
obj* l_Lean_Parser_Command_noncomputable;
obj* l_Lean_Parser_Term_optType___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_commandParserFn(uint8);
obj* l_Lean_Parser_Command_private___closed__1;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_attrInstance___elambda__1___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declId___closed__3;
obj* l_Lean_Parser_Command_noncomputable___closed__3;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__4;
obj* l_Lean_Parser_Command_def___elambda__1___closed__5;
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Command_attributes___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_attrInstance___elambda__1___spec__1(uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_protected___elambda__1___rarg___closed__4;
obj* l_Lean_Parser_Command_attributes;
obj* l_Lean_Parser_Command_theorem___elambda__1___closed__4;
obj* l_Lean_Parser_Command_noncomputable___elambda__1___boxed(obj*);
obj* l_Lean_Parser_Command_attributes___closed__4;
obj* l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__5;
obj* l_Lean_Parser_Command_optDeclSig___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_protected___closed__4;
extern obj* l_Lean_Parser_Term_list___elambda__1___closed__8;
obj* l_Lean_Parser_Command_def___closed__4;
obj* l_Lean_Parser_Command_protected___elambda__1___rarg___closed__1;
obj* l_Lean_Parser_Command_docComment___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__6;
obj* l_Lean_Parser_Command_docComment___closed__5;
obj* l_Lean_Parser_Command_optDeclSig___elambda__1___closed__1;
obj* l_Lean_Parser_Command_attributes___closed__3;
obj* l_Lean_Parser_Command_attrArg___closed__1;
obj* l_Lean_Parser_Command_protected___closed__2;
obj* l_Lean_Parser_Command_private;
obj* l_Lean_Parser_regBuiltinCommandParserAttr___closed__4;
obj* l_Lean_Parser_Command_attributes___closed__2;
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__1(obj*, uint8, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_protected___elambda__1___rarg___closed__3;
obj* l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__8;
extern obj* l_Lean_Parser_Term_typeSpec;
extern obj* l_Lean_Parser_Term_id___closed__1;
obj* l_Lean_Parser_Command_declSig___closed__2;
obj* l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__3;
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_attributes___elambda__1___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Command_declId___elambda__1___closed__1;
obj* l_Lean_Parser_Command_def___closed__6;
obj* l_Lean_Parser_Command_attrInstance___elambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_commentBody___elambda__1___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Command_declId___elambda__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Command_optDeclSig___closed__1;
obj* l_Lean_Parser_Command_declModifiers___closed__8;
obj* l_Lean_Parser_Command_attrArg;
obj* l_Lean_Parser_Command_private___elambda__1___rarg___closed__2;
obj* l_Lean_Parser_mkBuiltinParsingTablesRef(obj*);
obj* _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("builtinCommandParser");
return x_1;
}
}
obj* _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("builtinCommandParsingTable");
return x_1;
}
}
obj* _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_regBuiltinCommandParserAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__2;
x_3 = l_Lean_Parser_regBuiltinCommandParserAttr___closed__4;
x_4 = l_Lean_Parser_registerBuiltinParserAttribute(x_2, x_3, x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_commandParserFn___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("command");
return x_1;
}
}
obj* l_Lean_Parser_commandParserFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_commandParserFn___rarg___closed__1;
x_6 = l_Lean_Parser_builtinCommandParsingTable;
x_7 = l_Lean_Parser_runBuiltinParserUnsafe(x_5, x_6, x_1, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_commandParserFn(uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_commandParserFn___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_commandParserFn___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_commandParserFn___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_commandParserFn___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Lean_Parser_commandParserFn(x_2);
return x_3;
}
}
obj* l_Lean_Parser_commandParser___elambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_commandParserFn___rarg___closed__1;
x_6 = l_Lean_Parser_builtinCommandParsingTable;
x_7 = l_Lean_Parser_runBuiltinParserUnsafe(x_5, x_6, x_1, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_commandParser(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_commandParser___elambda__1___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_Lean_Parser_Parser_inhabited___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_commandParser___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_commandParser___elambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_Command_commentBody___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(1u);
x_4 = l_Lean_Parser_finishCommentBlock___main(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_Command_commentBody___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_commentBody___elambda__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_commentBody___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_commentBody___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_commentBody___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Parser_inhabited___closed__1;
x_2 = l_Lean_Parser_Command_commentBody___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_commentBody() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_commentBody___closed__2;
return x_1;
}
}
obj* l_Lean_Parser_Command_commentBody___elambda__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Command_commentBody___elambda__1___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Command_commentBody___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Command_commentBody___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Command");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("docComment");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("/--");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_2 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__6;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__7;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_docComment___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__6;
x_6 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__8;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::mk_nat_obj(1u);
x_10 = l_Lean_Parser_finishCommentBlock___main(x_9, x_1, x_7);
lean::dec(x_1);
x_11 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__4;
x_12 = l_Lean_Parser_ParserState_mkNode(x_10, x_11, x_4);
return x_12;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_8);
lean::dec(x_1);
x_13 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__4;
x_14 = l_Lean_Parser_ParserState_mkNode(x_7, x_13, x_4);
return x_14;
}
}
}
obj* l_Lean_Parser_Command_docComment___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_docComment___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_docComment___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__6;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_docComment___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_Command_commentBody;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Command_docComment___closed__1;
x_4 = l_Lean_Parser_andthenInfo(x_3, x_2);
return x_4;
}
}
obj* _init_l_Lean_Parser_Command_docComment___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_docComment___closed__2;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_docComment___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_docComment___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_docComment___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___closed__3;
x_2 = l_Lean_Parser_Command_docComment___closed__4;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_docComment() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_docComment___closed__5;
return x_1;
}
}
obj* l_Lean_Parser_Command_docComment___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Command_docComment___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Command_attrArg___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::inc(x_1);
x_6 = l_Lean_Parser_identFn___rarg(x_1, x_2);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_8; uint8 x_9; 
lean::dec(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
x_9 = lean::nat_dec_eq(x_8, x_5);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::inc(x_5);
x_10 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_12 = lean::array_get_size(x_11);
lean::dec(x_11);
lean::inc(x_1);
x_13 = l_Lean_Parser_strLitFn___rarg(x_1, x_10);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_1);
return x_13;
}
else
{
obj* x_15; uint8 x_16; 
lean::dec(x_14);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
x_16 = lean::nat_dec_eq(x_15, x_5);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_1);
return x_13;
}
else
{
obj* x_17; obj* x_18; 
x_17 = l_Lean_Parser_ParserState_restore(x_13, x_12, x_5);
lean::dec(x_12);
x_18 = l_Lean_Parser_numLitFn___rarg(x_1, x_17);
return x_18;
}
}
}
}
}
}
obj* l_Lean_Parser_Command_attrArg___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_attrArg___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_attrArg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_strLit___closed__1;
x_2 = l_Lean_Parser_numLit___closed__1;
x_3 = l_Lean_Parser_orelseInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attrArg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_ident___closed__2;
x_2 = l_Lean_Parser_Command_attrArg___closed__1;
x_3 = l_Lean_Parser_orelseInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attrArg___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_attrArg___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_attrArg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_attrArg___closed__2;
x_2 = l_Lean_Parser_Command_attrArg___closed__3;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attrArg() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_attrArg___closed__4;
return x_1;
}
}
obj* l_Lean_Parser_Command_attrArg___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Command_attrArg___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_attrInstance___elambda__1___spec__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::array_get_size(x_5);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::inc(x_3);
x_8 = l_Lean_Parser_Command_attrArg___elambda__1___rarg(x_3, x_4);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; uint8 x_11; 
lean::dec(x_6);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
x_11 = lean::nat_dec_eq(x_7, x_10);
lean::dec(x_10);
lean::dec(x_7);
if (x_11 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_3);
x_13 = l_Lean_Parser_manyAux___main___closed__1;
x_14 = l_Lean_Parser_ParserState_mkError(x_8, x_13);
return x_14;
}
}
else
{
obj* x_15; 
lean::dec(x_9);
lean::dec(x_3);
x_15 = l_Lean_Parser_ParserState_restore(x_8, x_6, x_7);
lean::dec(x_6);
return x_15;
}
}
}
obj* _init_l_Lean_Parser_Command_attrInstance___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("attrInstance");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_attrInstance___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_attrInstance___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_attrInstance___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
lean::inc(x_2);
x_6 = l_Lean_Parser_identFn___rarg(x_2, x_3);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = 0;
x_11 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_attrInstance___elambda__1___spec__1(x_10, x_1, x_2, x_6);
x_12 = l_Lean_nullKind;
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_9);
x_14 = l_Lean_Parser_Command_attrInstance___elambda__1___closed__2;
x_15 = l_Lean_Parser_ParserState_mkNode(x_13, x_14, x_5);
return x_15;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_7);
lean::dec(x_2);
x_16 = l_Lean_Parser_Command_attrInstance___elambda__1___closed__2;
x_17 = l_Lean_Parser_ParserState_mkNode(x_6, x_16, x_5);
return x_17;
}
}
}
obj* _init_l_Lean_Parser_Command_attrInstance___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_attrArg;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attrInstance___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_ident___closed__2;
x_2 = l_Lean_Parser_Command_attrInstance___closed__1;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attrInstance___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_attrInstance___closed__2;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_attrInstance___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_attrInstance___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_attrInstance___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_attrInstance___closed__3;
x_2 = l_Lean_Parser_Command_attrInstance___closed__4;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attrInstance() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_attrInstance___closed__5;
return x_1;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_attrInstance___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_attrInstance___elambda__1___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_Command_attrInstance___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Command_attrInstance___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_attributes___elambda__1___spec__2(uint8 x_1, uint8 x_2, obj* x_3, uint8 x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::inc(x_6);
x_11 = l_Lean_Parser_Command_attrInstance___elambda__1(x_5, x_6, x_7);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_10);
lean::dec(x_9);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_14 = lean::array_get_size(x_13);
lean::dec(x_13);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
x_16 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2___closed__1;
x_17 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2___closed__3;
lean::inc(x_6);
x_18 = l_Lean_Parser_symbolFnAux(x_16, x_17, x_6, x_11);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
lean::dec(x_15);
lean::dec(x_14);
{
uint8 _tmp_3 = x_2;
obj* _tmp_6 = x_18;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_19);
lean::dec(x_6);
x_21 = l_Lean_Parser_ParserState_restore(x_18, x_14, x_15);
lean::dec(x_14);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_3);
return x_23;
}
}
else
{
lean::dec(x_12);
lean::dec(x_6);
if (x_4 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_10);
lean::dec(x_9);
x_24 = lean::box(0);
x_25 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_24);
x_26 = l_Lean_nullKind;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_3);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
lean::dec(x_9);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_3);
return x_30;
}
}
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_attributes___elambda__1___spec__1(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = 0;
x_9 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_attributes___elambda__1___spec__2(x_1, x_2, x_7, x_8, x_3, x_4, x_5);
return x_9;
}
}
obj* _init_l_Lean_Parser_Command_attributes___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("attributes");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_attributes___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_attributes___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attributes___elambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("@[");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_attributes___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_attributes___elambda__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_attributes___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_2 = l_Lean_Parser_Command_attributes___elambda__1___closed__4;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attributes___elambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_attributes___elambda__1___closed__5;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_attributes___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Command_attributes___elambda__1___closed__4;
x_7 = l_Lean_Parser_Command_attributes___elambda__1___closed__6;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; uint8 x_11; obj* x_12; obj* x_13; 
x_10 = 0;
x_11 = 0;
lean::inc(x_2);
x_12 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_attributes___elambda__1___spec__1(x_10, x_11, x_1, x_2, x_8);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = l_Lean_Parser_Term_list___elambda__1___closed__4;
x_15 = l_Lean_Parser_Term_list___elambda__1___closed__8;
x_16 = l_Lean_Parser_symbolFnAux(x_14, x_15, x_2, x_12);
x_17 = l_Lean_Parser_Command_attributes___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_16, x_17, x_5);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_13);
lean::dec(x_2);
x_19 = l_Lean_Parser_Command_attributes___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_12, x_19, x_5);
return x_20;
}
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_9);
lean::dec(x_2);
x_21 = l_Lean_Parser_Command_attributes___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_8, x_21, x_5);
return x_22;
}
}
}
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Command_attributes___spec__1(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_attributes___elambda__1___spec__1(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Command_attributes___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Command_attributes___elambda__1___closed__4;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attributes___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_Command_attrInstance;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Term_id___closed__2;
x_4 = l_Lean_Parser_sepBy1Info(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_Command_attributes___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_attributes___closed__2;
x_2 = l_Lean_Parser_Term_list___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attributes___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_attributes___closed__1;
x_2 = l_Lean_Parser_Command_attributes___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attributes___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_attributes___closed__4;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_attributes___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_attributes___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_attributes___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_attributes___closed__5;
x_2 = l_Lean_Parser_Command_attributes___closed__6;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_attributes() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_attributes___closed__7;
return x_1;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_attributes___elambda__1___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; uint8 x_10; obj* x_11; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_4);
lean::dec(x_4);
x_11 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_attributes___elambda__1___spec__2(x_8, x_9, x_3, x_10, x_5, x_6, x_7);
lean::dec(x_5);
return x_11;
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_attributes___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_attributes___elambda__1___spec__1(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_Command_attributes___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Command_attributes___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Command_attributes___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Command_attributes___spec__1(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* _init_l_Lean_Parser_Command_private___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("private");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_private___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_private___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_private___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_private___elambda__1___rarg___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_private___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_2 = l_Lean_Parser_Command_private___elambda__1___rarg___closed__3;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_private___elambda__1___rarg___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_private___elambda__1___rarg___closed__4;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_private___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Command_private___elambda__1___rarg___closed__3;
x_6 = l_Lean_Parser_Command_private___elambda__1___rarg___closed__5;
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Command_private___elambda__1___rarg___closed__2;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
obj* l_Lean_Parser_Command_private___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_private___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_private___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Command_private___elambda__1___rarg___closed__3;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_private___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_private___closed__1;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_private___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_private___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_private___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_private___closed__2;
x_2 = l_Lean_Parser_Command_private___closed__3;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_private() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_private___closed__4;
return x_1;
}
}
obj* l_Lean_Parser_Command_private___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Command_private___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_protected___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("protected");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_protected___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_protected___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_protected___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_protected___elambda__1___rarg___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_protected___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_2 = l_Lean_Parser_Command_protected___elambda__1___rarg___closed__3;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_protected___elambda__1___rarg___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_protected___elambda__1___rarg___closed__4;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_protected___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Command_protected___elambda__1___rarg___closed__3;
x_6 = l_Lean_Parser_Command_protected___elambda__1___rarg___closed__5;
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Command_protected___elambda__1___rarg___closed__2;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
obj* l_Lean_Parser_Command_protected___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_protected___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_protected___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Command_protected___elambda__1___rarg___closed__3;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_protected___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_protected___closed__1;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_protected___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_protected___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_protected___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_protected___closed__2;
x_2 = l_Lean_Parser_Command_protected___closed__3;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_protected() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_protected___closed__4;
return x_1;
}
}
obj* l_Lean_Parser_Command_protected___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Command_protected___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Command_visibility___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::inc(x_1);
x_6 = l_Lean_Parser_Command_private___elambda__1___rarg(x_1, x_2);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_8; uint8 x_9; 
lean::dec(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
x_9 = lean::nat_dec_eq(x_8, x_5);
lean::dec(x_8);
if (x_9 == 0)
{
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_10; obj* x_11; 
x_10 = l_Lean_Parser_ParserState_restore(x_6, x_4, x_5);
lean::dec(x_4);
x_11 = l_Lean_Parser_Command_protected___elambda__1___rarg(x_1, x_10);
return x_11;
}
}
}
}
obj* l_Lean_Parser_Command_visibility___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_visibility___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_visibility___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_Command_private;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Command_protected;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_2, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Command_visibility___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_visibility___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_visibility___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_visibility___closed__1;
x_2 = l_Lean_Parser_Command_visibility___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_visibility() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_visibility___closed__3;
return x_1;
}
}
obj* l_Lean_Parser_Command_visibility___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Command_visibility___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("noncomputable");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_2 = l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__3;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__4;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_noncomputable___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__3;
x_6 = l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__5;
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__2;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
obj* l_Lean_Parser_Command_noncomputable___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_noncomputable___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_noncomputable___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__3;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_noncomputable___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_noncomputable___closed__1;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_noncomputable___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_noncomputable___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_noncomputable___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_noncomputable___closed__2;
x_2 = l_Lean_Parser_Command_noncomputable___closed__3;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_noncomputable() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_noncomputable___closed__4;
return x_1;
}
}
obj* l_Lean_Parser_Command_noncomputable___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Command_noncomputable___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unsafe");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_2 = l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__3;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__4;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_unsafe___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__3;
x_6 = l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__5;
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__2;
x_9 = l_Lean_Parser_ParserState_mkNode(x_7, x_8, x_4);
return x_9;
}
}
obj* l_Lean_Parser_Command_unsafe___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_unsafe___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_unsafe___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__3;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_unsafe___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_unsafe___closed__1;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_unsafe___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_unsafe___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_unsafe___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_unsafe___closed__2;
x_2 = l_Lean_Parser_Command_unsafe___closed__3;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_unsafe() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_unsafe___closed__4;
return x_1;
}
}
obj* l_Lean_Parser_Command_unsafe___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Command_unsafe___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("declModifiers");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_declModifiers___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_declModifiers___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_31; obj* x_50; obj* x_69; obj* x_88; obj* x_89; obj* x_90; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_88 = lean::cnstr_get(x_3, 1);
lean::inc(x_88);
lean::inc(x_2);
x_89 = l_Lean_Parser_Command_docComment___elambda__1___rarg(x_2, x_3);
x_90 = lean::cnstr_get(x_89, 3);
lean::inc(x_90);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; obj* x_92; 
lean::dec(x_88);
x_91 = l_Lean_nullKind;
lean::inc(x_5);
x_92 = l_Lean_Parser_ParserState_mkNode(x_89, x_91, x_5);
x_69 = x_92;
goto block_87;
}
else
{
obj* x_93; uint8 x_94; 
lean::dec(x_90);
x_93 = lean::cnstr_get(x_89, 1);
lean::inc(x_93);
x_94 = lean::nat_dec_eq(x_93, x_88);
lean::dec(x_93);
if (x_94 == 0)
{
obj* x_95; obj* x_96; 
lean::dec(x_88);
x_95 = l_Lean_nullKind;
lean::inc(x_5);
x_96 = l_Lean_Parser_ParserState_mkNode(x_89, x_95, x_5);
x_69 = x_96;
goto block_87;
}
else
{
obj* x_97; obj* x_98; obj* x_99; 
x_97 = l_Lean_Parser_ParserState_restore(x_89, x_5, x_88);
x_98 = l_Lean_nullKind;
lean::inc(x_5);
x_99 = l_Lean_Parser_ParserState_mkNode(x_97, x_98, x_5);
x_69 = x_99;
goto block_87;
}
}
block_30:
{
obj* x_7; 
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
x_11 = l_Lean_Parser_Command_unsafe___elambda__1___rarg(x_2, x_6);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_10);
x_13 = l_Lean_nullKind;
x_14 = l_Lean_Parser_ParserState_mkNode(x_11, x_13, x_9);
x_15 = l_Lean_Parser_Command_declModifiers___elambda__1___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_5);
return x_16;
}
else
{
obj* x_17; uint8 x_18; 
lean::dec(x_12);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
x_18 = lean::nat_dec_eq(x_17, x_10);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_10);
x_19 = l_Lean_nullKind;
x_20 = l_Lean_Parser_ParserState_mkNode(x_11, x_19, x_9);
x_21 = l_Lean_Parser_Command_declModifiers___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_20, x_21, x_5);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
x_24 = l_Lean_nullKind;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_9);
x_26 = l_Lean_Parser_Command_declModifiers___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_5);
return x_27;
}
}
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_7);
lean::dec(x_2);
x_28 = l_Lean_Parser_Command_declModifiers___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_6, x_28, x_5);
return x_29;
}
}
block_49:
{
obj* x_32; 
x_32 = lean::cnstr_get(x_31, 3);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
x_34 = lean::array_get_size(x_33);
lean::dec(x_33);
x_35 = lean::cnstr_get(x_31, 1);
lean::inc(x_35);
lean::inc(x_2);
x_36 = l_Lean_Parser_Command_noncomputable___elambda__1___rarg(x_2, x_31);
x_37 = lean::cnstr_get(x_36, 3);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_39; 
lean::dec(x_35);
x_38 = l_Lean_nullKind;
x_39 = l_Lean_Parser_ParserState_mkNode(x_36, x_38, x_34);
x_6 = x_39;
goto block_30;
}
else
{
obj* x_40; uint8 x_41; 
lean::dec(x_37);
x_40 = lean::cnstr_get(x_36, 1);
lean::inc(x_40);
x_41 = lean::nat_dec_eq(x_40, x_35);
lean::dec(x_40);
if (x_41 == 0)
{
obj* x_42; obj* x_43; 
lean::dec(x_35);
x_42 = l_Lean_nullKind;
x_43 = l_Lean_Parser_ParserState_mkNode(x_36, x_42, x_34);
x_6 = x_43;
goto block_30;
}
else
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_Lean_Parser_ParserState_restore(x_36, x_34, x_35);
x_45 = l_Lean_nullKind;
x_46 = l_Lean_Parser_ParserState_mkNode(x_44, x_45, x_34);
x_6 = x_46;
goto block_30;
}
}
}
else
{
obj* x_47; obj* x_48; 
lean::dec(x_32);
lean::dec(x_2);
x_47 = l_Lean_Parser_Command_declModifiers___elambda__1___closed__2;
x_48 = l_Lean_Parser_ParserState_mkNode(x_31, x_47, x_5);
return x_48;
}
}
block_68:
{
obj* x_51; 
x_51 = lean::cnstr_get(x_50, 3);
lean::inc(x_51);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_52 = lean::cnstr_get(x_50, 0);
lean::inc(x_52);
x_53 = lean::array_get_size(x_52);
lean::dec(x_52);
x_54 = lean::cnstr_get(x_50, 1);
lean::inc(x_54);
lean::inc(x_2);
x_55 = l_Lean_Parser_Command_visibility___elambda__1___rarg(x_2, x_50);
x_56 = lean::cnstr_get(x_55, 3);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; 
lean::dec(x_54);
x_57 = l_Lean_nullKind;
x_58 = l_Lean_Parser_ParserState_mkNode(x_55, x_57, x_53);
x_31 = x_58;
goto block_49;
}
else
{
obj* x_59; uint8 x_60; 
lean::dec(x_56);
x_59 = lean::cnstr_get(x_55, 1);
lean::inc(x_59);
x_60 = lean::nat_dec_eq(x_59, x_54);
lean::dec(x_59);
if (x_60 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_54);
x_61 = l_Lean_nullKind;
x_62 = l_Lean_Parser_ParserState_mkNode(x_55, x_61, x_53);
x_31 = x_62;
goto block_49;
}
else
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_Lean_Parser_ParserState_restore(x_55, x_53, x_54);
x_64 = l_Lean_nullKind;
x_65 = l_Lean_Parser_ParserState_mkNode(x_63, x_64, x_53);
x_31 = x_65;
goto block_49;
}
}
}
else
{
obj* x_66; obj* x_67; 
lean::dec(x_51);
lean::dec(x_2);
x_66 = l_Lean_Parser_Command_declModifiers___elambda__1___closed__2;
x_67 = l_Lean_Parser_ParserState_mkNode(x_50, x_66, x_5);
return x_67;
}
}
block_87:
{
obj* x_70; 
x_70 = lean::cnstr_get(x_69, 3);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
x_72 = lean::array_get_size(x_71);
lean::dec(x_71);
x_73 = lean::cnstr_get(x_69, 1);
lean::inc(x_73);
lean::inc(x_2);
x_74 = l_Lean_Parser_Command_attributes___elambda__1(x_1, x_2, x_69);
x_75 = lean::cnstr_get(x_74, 3);
lean::inc(x_75);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_77; 
lean::dec(x_73);
x_76 = l_Lean_nullKind;
x_77 = l_Lean_Parser_ParserState_mkNode(x_74, x_76, x_72);
x_50 = x_77;
goto block_68;
}
else
{
obj* x_78; uint8 x_79; 
lean::dec(x_75);
x_78 = lean::cnstr_get(x_74, 1);
lean::inc(x_78);
x_79 = lean::nat_dec_eq(x_78, x_73);
lean::dec(x_78);
if (x_79 == 0)
{
obj* x_80; obj* x_81; 
lean::dec(x_73);
x_80 = l_Lean_nullKind;
x_81 = l_Lean_Parser_ParserState_mkNode(x_74, x_80, x_72);
x_50 = x_81;
goto block_68;
}
else
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = l_Lean_Parser_ParserState_restore(x_74, x_72, x_73);
x_83 = l_Lean_nullKind;
x_84 = l_Lean_Parser_ParserState_mkNode(x_82, x_83, x_72);
x_50 = x_84;
goto block_68;
}
}
}
else
{
obj* x_85; obj* x_86; 
lean::dec(x_70);
lean::dec(x_2);
x_85 = l_Lean_Parser_Command_declModifiers___elambda__1___closed__2;
x_86 = l_Lean_Parser_ParserState_mkNode(x_69, x_85, x_5);
return x_86;
}
}
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_attributes;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_visibility;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_noncomputable;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_unsafe;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_noFirstTokenInfo(x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_declModifiers___closed__4;
x_2 = l_Lean_Parser_Command_declModifiers___closed__5;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_declModifiers___closed__3;
x_2 = l_Lean_Parser_Command_declModifiers___closed__6;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_declModifiers___closed__2;
x_2 = l_Lean_Parser_Command_declModifiers___closed__7;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__9() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_declModifiers___closed__1;
x_2 = l_Lean_Parser_Command_declModifiers___closed__8;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__10() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_declModifiers___closed__9;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__11() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_declModifiers___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers___closed__12() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_declModifiers___closed__10;
x_2 = l_Lean_Parser_Command_declModifiers___closed__11;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declModifiers() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_declModifiers___closed__12;
return x_1;
}
}
obj* l_Lean_Parser_Command_declModifiers___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Command_declModifiers___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_declId___elambda__1___spec__2(uint8 x_1, uint8 x_2, obj* x_3, uint8 x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::inc(x_6);
x_11 = l_Lean_Parser_identFn___rarg(x_6, x_7);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_10);
lean::dec(x_9);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_14 = lean::array_get_size(x_13);
lean::dec(x_13);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
x_16 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2___closed__1;
x_17 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Term_id___elambda__1___spec__2___closed__3;
lean::inc(x_6);
x_18 = l_Lean_Parser_symbolFnAux(x_16, x_17, x_6, x_11);
x_19 = lean::cnstr_get(x_18, 3);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
lean::dec(x_15);
lean::dec(x_14);
{
uint8 _tmp_3 = x_2;
obj* _tmp_6 = x_18;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_19);
lean::dec(x_6);
x_21 = l_Lean_Parser_ParserState_restore(x_18, x_14, x_15);
lean::dec(x_14);
x_22 = l_Lean_nullKind;
x_23 = l_Lean_Parser_ParserState_mkNode(x_21, x_22, x_3);
return x_23;
}
}
else
{
lean::dec(x_12);
lean::dec(x_6);
if (x_4 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_10);
lean::dec(x_9);
x_24 = lean::box(0);
x_25 = l_Lean_Parser_ParserState_pushSyntax(x_11, x_24);
x_26 = l_Lean_nullKind;
x_27 = l_Lean_Parser_ParserState_mkNode(x_25, x_26, x_3);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_Lean_Parser_ParserState_restore(x_11, x_9, x_10);
lean::dec(x_9);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_28, x_29, x_3);
return x_30;
}
}
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_declId___elambda__1___spec__1(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = 0;
x_9 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_declId___elambda__1___spec__2(x_1, x_2, x_7, x_8, x_3, x_4, x_5);
return x_9;
}
}
obj* _init_l_Lean_Parser_Command_declId___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("declId");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declId___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_declId___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_declId___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
lean::inc(x_2);
x_6 = l_Lean_Parser_identFn___rarg(x_2, x_3);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_9 = lean::array_get_size(x_8);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
x_11 = l_Lean_Parser_Term_id___elambda__1___closed__6;
x_12 = l_Lean_Parser_Term_id___elambda__1___closed__9;
lean::inc(x_2);
x_13 = l_Lean_Parser_symbolFnAux(x_11, x_12, x_2, x_6);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; uint8 x_16; obj* x_17; obj* x_18; 
x_15 = 0;
x_16 = 0;
lean::inc(x_2);
x_17 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_declId___elambda__1___spec__1(x_15, x_16, x_1, x_2, x_13);
x_18 = lean::cnstr_get(x_17, 3);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = l_Lean_Parser_Term_id___elambda__1___closed__7;
x_20 = l_Lean_Parser_Term_id___elambda__1___closed__11;
x_21 = l_Lean_Parser_symbolFnAux(x_19, x_20, x_2, x_17);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
x_23 = l_Lean_nullKind;
x_24 = l_Lean_Parser_ParserState_mkNode(x_21, x_23, x_9);
x_25 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_26 = l_Lean_Parser_ParserState_mkNode(x_24, x_25, x_5);
return x_26;
}
else
{
obj* x_27; uint8 x_28; 
lean::dec(x_22);
x_27 = lean::cnstr_get(x_21, 1);
lean::inc(x_27);
x_28 = lean::nat_dec_eq(x_27, x_10);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_10);
x_29 = l_Lean_nullKind;
x_30 = l_Lean_Parser_ParserState_mkNode(x_21, x_29, x_9);
x_31 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_32 = l_Lean_Parser_ParserState_mkNode(x_30, x_31, x_5);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = l_Lean_Parser_ParserState_restore(x_21, x_9, x_10);
x_34 = l_Lean_nullKind;
x_35 = l_Lean_Parser_ParserState_mkNode(x_33, x_34, x_9);
x_36 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_37 = l_Lean_Parser_ParserState_mkNode(x_35, x_36, x_5);
return x_37;
}
}
}
else
{
obj* x_38; uint8 x_39; 
lean::dec(x_18);
lean::dec(x_2);
x_38 = lean::cnstr_get(x_17, 1);
lean::inc(x_38);
x_39 = lean::nat_dec_eq(x_38, x_10);
lean::dec(x_38);
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_10);
x_40 = l_Lean_nullKind;
x_41 = l_Lean_Parser_ParserState_mkNode(x_17, x_40, x_9);
x_42 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_43 = l_Lean_Parser_ParserState_mkNode(x_41, x_42, x_5);
return x_43;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_44 = l_Lean_Parser_ParserState_restore(x_17, x_9, x_10);
x_45 = l_Lean_nullKind;
x_46 = l_Lean_Parser_ParserState_mkNode(x_44, x_45, x_9);
x_47 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_48 = l_Lean_Parser_ParserState_mkNode(x_46, x_47, x_5);
return x_48;
}
}
}
else
{
obj* x_49; uint8 x_50; 
lean::dec(x_14);
lean::dec(x_2);
x_49 = lean::cnstr_get(x_13, 1);
lean::inc(x_49);
x_50 = lean::nat_dec_eq(x_49, x_10);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_10);
x_51 = l_Lean_nullKind;
x_52 = l_Lean_Parser_ParserState_mkNode(x_13, x_51, x_9);
x_53 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_54 = l_Lean_Parser_ParserState_mkNode(x_52, x_53, x_5);
return x_54;
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_55 = l_Lean_Parser_ParserState_restore(x_13, x_9, x_10);
x_56 = l_Lean_nullKind;
x_57 = l_Lean_Parser_ParserState_mkNode(x_55, x_56, x_9);
x_58 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_59 = l_Lean_Parser_ParserState_mkNode(x_57, x_58, x_5);
return x_59;
}
}
}
else
{
obj* x_60; obj* x_61; 
lean::dec(x_7);
lean::dec(x_2);
x_60 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_61 = l_Lean_Parser_ParserState_mkNode(x_6, x_60, x_5);
return x_61;
}
}
}
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Command_declId___spec__1(uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_declId___elambda__1___spec__1(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_Command_declId___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_ident___closed__2;
x_2 = l_Lean_Parser_Term_id___closed__2;
x_3 = l_Lean_Parser_sepBy1Info(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declId___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_declId___closed__1;
x_2 = l_Lean_Parser_Term_id___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declId___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Term_id___closed__1;
x_2 = l_Lean_Parser_Command_declId___closed__2;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declId___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_declId___closed__3;
x_2 = l_Lean_Parser_noFirstTokenInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_declId___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_ident___closed__2;
x_2 = l_Lean_Parser_Command_declId___closed__4;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declId___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_declId___closed__5;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_declId___closed__7() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_declId___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declId___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_declId___closed__6;
x_2 = l_Lean_Parser_Command_declId___closed__7;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declId() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_declId___closed__8;
return x_1;
}
}
obj* l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_declId___elambda__1___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; uint8 x_9; uint8 x_10; obj* x_11; 
x_8 = lean::unbox(x_1);
lean::dec(x_1);
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = lean::unbox(x_4);
lean::dec(x_4);
x_11 = l___private_init_lean_parser_parser_1__sepByFnAux___main___at_Lean_Parser_Command_declId___elambda__1___spec__2(x_8, x_9, x_3, x_10, x_5, x_6, x_7);
lean::dec(x_5);
return x_11;
}
}
obj* l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_declId___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepBy1Fn___main___at_Lean_Parser_Command_declId___elambda__1___spec__1(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_Command_declId___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Command_declId___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Command_declId___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
lean::dec(x_1);
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_sepBy1Fn___at_Lean_Parser_Command_declId___spec__1(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* _init_l_Lean_Parser_Command_declSig___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("declSig");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declSig___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_declSig___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_declSig___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1___closed__1;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
lean::inc(x_5);
lean::inc(x_2);
lean::inc(x_1);
x_8 = lean::apply_3(x_5, x_1, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = 0;
lean::inc(x_2);
x_11 = l_Lean_Parser_manyAux___main(x_10, x_5, x_1, x_2, x_8);
x_12 = l_Lean_nullKind;
lean::inc(x_7);
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_7);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = l_Lean_Parser_Term_typeSpec___elambda__1___rarg(x_2, x_13);
x_16 = l_Lean_Parser_Command_declSig___elambda__1___closed__2;
x_17 = l_Lean_Parser_ParserState_mkNode(x_15, x_16, x_7);
return x_17;
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_14);
lean::dec(x_2);
x_18 = l_Lean_Parser_Command_declSig___elambda__1___closed__2;
x_19 = l_Lean_Parser_ParserState_mkNode(x_13, x_18, x_7);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_9);
lean::dec(x_5);
lean::dec(x_1);
x_20 = l_Lean_nullKind;
lean::inc(x_7);
x_21 = l_Lean_Parser_ParserState_mkNode(x_8, x_20, x_7);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_Lean_Parser_Term_typeSpec___elambda__1___rarg(x_2, x_21);
x_24 = l_Lean_Parser_Command_declSig___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_7);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_22);
lean::dec(x_2);
x_26 = l_Lean_Parser_Command_declSig___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_21, x_26, x_7);
return x_27;
}
}
}
}
obj* _init_l_Lean_Parser_Command_declSig___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1___closed__1;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Term_typeSpec;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Command_declSig___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_declSig___closed__1;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_declSig___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_declSig___elambda__1), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declSig___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_declSig___closed__2;
x_2 = l_Lean_Parser_Command_declSig___closed__3;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declSig() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_declSig___closed__4;
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_optDeclSig___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("optDeclSig");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_optDeclSig___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_optDeclSig___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_optDeclSig___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1___closed__1;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
lean::inc(x_5);
lean::inc(x_2);
lean::inc(x_1);
x_8 = lean::apply_3(x_5, x_1, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = 0;
lean::inc(x_2);
x_11 = l_Lean_Parser_manyAux___main(x_10, x_5, x_1, x_2, x_8);
x_12 = l_Lean_nullKind;
lean::inc(x_7);
x_13 = l_Lean_Parser_ParserState_mkNode(x_11, x_12, x_7);
x_14 = lean::cnstr_get(x_13, 3);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = l_Lean_Parser_Term_optType___elambda__1___rarg(x_2, x_13);
x_16 = l_Lean_Parser_Command_optDeclSig___elambda__1___closed__2;
x_17 = l_Lean_Parser_ParserState_mkNode(x_15, x_16, x_7);
return x_17;
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_14);
lean::dec(x_2);
x_18 = l_Lean_Parser_Command_optDeclSig___elambda__1___closed__2;
x_19 = l_Lean_Parser_ParserState_mkNode(x_13, x_18, x_7);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_9);
lean::dec(x_5);
lean::dec(x_1);
x_20 = l_Lean_nullKind;
lean::inc(x_7);
x_21 = l_Lean_Parser_ParserState_mkNode(x_8, x_20, x_7);
x_22 = lean::cnstr_get(x_21, 3);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_Lean_Parser_Term_optType___elambda__1___rarg(x_2, x_21);
x_24 = l_Lean_Parser_Command_optDeclSig___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_7);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_22);
lean::dec(x_2);
x_26 = l_Lean_Parser_Command_optDeclSig___elambda__1___closed__2;
x_27 = l_Lean_Parser_ParserState_mkNode(x_21, x_26, x_7);
return x_27;
}
}
}
}
obj* _init_l_Lean_Parser_Command_optDeclSig___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_forall___elambda__1___spec__1___closed__1;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Term_optType;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Command_optDeclSig___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_optDeclSig___closed__1;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_optDeclSig___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_optDeclSig___elambda__1), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_optDeclSig___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_optDeclSig___closed__2;
x_2 = l_Lean_Parser_Command_optDeclSig___closed__3;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_optDeclSig() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_optDeclSig___closed__4;
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("declValSimple");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_declValSimple___elambda__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__3;
x_6 = l_Lean_Parser_Term_haveAssign___elambda__1___rarg___closed__5;
lean::inc(x_1);
x_7 = l_Lean_Parser_symbolFnAux(x_5, x_6, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_Lean_Parser_termParserFn___rarg___closed__1;
x_10 = l_Lean_Parser_builtinTermParsingTable;
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Lean_Parser_runBuiltinParserUnsafe(x_9, x_10, x_11, x_1, x_7);
x_13 = l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__2;
x_14 = l_Lean_Parser_ParserState_mkNode(x_12, x_13, x_4);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
lean::dec(x_8);
lean::dec(x_1);
x_15 = l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_7, x_15, x_4);
return x_16;
}
}
}
obj* l_Lean_Parser_Command_declValSimple___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_declValSimple___elambda__1___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_declValSimple___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_declValSimple___elambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declValSimple___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Term_haveAssign___closed__3;
x_2 = l_Lean_Parser_Command_declValSimple___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declValSimple() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_declValSimple___closed__2;
return x_1;
}
}
obj* l_Lean_Parser_Command_declValSimple___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Command_declValSimple___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__1(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_21 = lean::cnstr_get(x_4, 3);
lean::inc(x_21);
x_22 = l_Lean_FileMap_toPosition___main(x_21, x_8);
lean::dec(x_21);
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_24 = lean::nat_dec_le(x_1, x_23);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_letEqns___elambda__1___spec__1___closed__1;
x_26 = l_Lean_Parser_ParserState_mkError(x_5, x_25);
x_9 = x_26;
goto block_20;
}
else
{
x_9 = x_5;
goto block_20;
}
block_20:
{
obj* x_10; 
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
lean::inc(x_4);
x_11 = l_Lean_Parser_Term_equation___elambda__1(x_3, x_4, x_9);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; uint8 x_14; 
lean::dec(x_7);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
x_14 = lean::nat_dec_eq(x_8, x_13);
lean::dec(x_13);
lean::dec(x_8);
if (x_14 == 0)
{
x_5 = x_11;
goto _start;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_4);
x_16 = l_Lean_Parser_manyAux___main___closed__1;
x_17 = l_Lean_Parser_ParserState_mkError(x_11, x_16);
return x_17;
}
}
else
{
obj* x_18; 
lean::dec(x_12);
lean::dec(x_4);
x_18 = l_Lean_Parser_ParserState_restore(x_11, x_7, x_8);
lean::dec(x_7);
return x_18;
}
}
else
{
obj* x_19; 
lean::dec(x_10);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean::dec(x_7);
return x_19;
}
}
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__2(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_21 = lean::cnstr_get(x_4, 3);
lean::inc(x_21);
x_22 = l_Lean_FileMap_toPosition___main(x_21, x_8);
lean::dec(x_21);
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_24 = lean::nat_dec_le(x_1, x_23);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_letEqns___elambda__1___spec__1___closed__1;
x_26 = l_Lean_Parser_ParserState_mkError(x_5, x_25);
x_9 = x_26;
goto block_20;
}
else
{
x_9 = x_5;
goto block_20;
}
block_20:
{
obj* x_10; 
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
lean::inc(x_4);
x_11 = l_Lean_Parser_Term_equation___elambda__1(x_3, x_4, x_9);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; uint8 x_14; 
lean::dec(x_7);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
x_14 = lean::nat_dec_eq(x_8, x_13);
lean::dec(x_13);
lean::dec(x_8);
if (x_14 == 0)
{
x_5 = x_11;
goto _start;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_4);
x_16 = l_Lean_Parser_manyAux___main___closed__1;
x_17 = l_Lean_Parser_ParserState_mkError(x_11, x_16);
return x_17;
}
}
else
{
obj* x_18; 
lean::dec(x_12);
lean::dec(x_4);
x_18 = l_Lean_Parser_ParserState_restore(x_11, x_7, x_8);
lean::dec(x_7);
return x_18;
}
}
else
{
obj* x_19; 
lean::dec(x_10);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean::dec(x_7);
return x_19;
}
}
}
}
obj* _init_l_Lean_Parser_Command_declValEqns___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("declValEqns");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declValEqns___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_declValEqns___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_declValEqns___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = lean::cnstr_get(x_2, 3);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
x_8 = l_Lean_FileMap_toPosition___main(x_6, x_7);
lean::dec(x_7);
lean::dec(x_6);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::nat_dec_le(x_9, x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_letEqns___elambda__1___spec__1___closed__1;
x_12 = l_Lean_Parser_ParserState_mkError(x_3, x_11);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; 
lean::inc(x_2);
x_14 = l_Lean_Parser_Term_equation___elambda__1(x_1, x_2, x_12);
x_15 = lean::cnstr_get(x_14, 3);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = 0;
x_17 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__1(x_9, x_16, x_1, x_2, x_14);
lean::dec(x_9);
x_18 = l_Lean_nullKind;
lean::inc(x_5);
x_19 = l_Lean_Parser_ParserState_mkNode(x_17, x_18, x_5);
x_20 = l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
x_21 = l_Lean_Parser_ParserState_mkNode(x_19, x_20, x_5);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_15);
lean::dec(x_9);
lean::dec(x_2);
x_22 = l_Lean_nullKind;
lean::inc(x_5);
x_23 = l_Lean_Parser_ParserState_mkNode(x_14, x_22, x_5);
x_24 = l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
x_25 = l_Lean_Parser_ParserState_mkNode(x_23, x_24, x_5);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_13);
lean::dec(x_9);
lean::dec(x_2);
x_26 = l_Lean_nullKind;
lean::inc(x_5);
x_27 = l_Lean_Parser_ParserState_mkNode(x_12, x_26, x_5);
x_28 = l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
x_29 = l_Lean_Parser_ParserState_mkNode(x_27, x_28, x_5);
return x_29;
}
}
else
{
obj* x_30; 
x_30 = lean::cnstr_get(x_3, 3);
lean::inc(x_30);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; 
lean::inc(x_2);
x_31 = l_Lean_Parser_Term_equation___elambda__1(x_1, x_2, x_3);
x_32 = lean::cnstr_get(x_31, 3);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = 0;
x_34 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__2(x_9, x_33, x_1, x_2, x_31);
lean::dec(x_9);
x_35 = l_Lean_nullKind;
lean::inc(x_5);
x_36 = l_Lean_Parser_ParserState_mkNode(x_34, x_35, x_5);
x_37 = l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
x_38 = l_Lean_Parser_ParserState_mkNode(x_36, x_37, x_5);
return x_38;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_9);
lean::dec(x_2);
x_39 = l_Lean_nullKind;
lean::inc(x_5);
x_40 = l_Lean_Parser_ParserState_mkNode(x_31, x_39, x_5);
x_41 = l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
x_42 = l_Lean_Parser_ParserState_mkNode(x_40, x_41, x_5);
return x_42;
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_30);
lean::dec(x_9);
lean::dec(x_2);
x_43 = l_Lean_nullKind;
lean::inc(x_5);
x_44 = l_Lean_Parser_ParserState_mkNode(x_3, x_43, x_5);
x_45 = l_Lean_Parser_Command_declValEqns___elambda__1___closed__2;
x_46 = l_Lean_Parser_ParserState_mkNode(x_44, x_45, x_5);
return x_46;
}
}
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___spec__1(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_21 = lean::cnstr_get(x_4, 3);
lean::inc(x_21);
x_22 = l_Lean_FileMap_toPosition___main(x_21, x_8);
lean::dec(x_21);
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_24 = lean::nat_dec_le(x_1, x_23);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_letEqns___elambda__1___spec__1___closed__1;
x_26 = l_Lean_Parser_ParserState_mkError(x_5, x_25);
x_9 = x_26;
goto block_20;
}
else
{
x_9 = x_5;
goto block_20;
}
block_20:
{
obj* x_10; 
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
lean::inc(x_4);
x_11 = l_Lean_Parser_Term_equation___elambda__1(x_3, x_4, x_9);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; uint8 x_14; 
lean::dec(x_7);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
x_14 = lean::nat_dec_eq(x_8, x_13);
lean::dec(x_13);
lean::dec(x_8);
if (x_14 == 0)
{
x_5 = x_11;
goto _start;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_4);
x_16 = l_Lean_Parser_manyAux___main___closed__1;
x_17 = l_Lean_Parser_ParserState_mkError(x_11, x_16);
return x_17;
}
}
else
{
obj* x_18; 
lean::dec(x_12);
lean::dec(x_4);
x_18 = l_Lean_Parser_ParserState_restore(x_11, x_7, x_8);
lean::dec(x_7);
return x_18;
}
}
else
{
obj* x_19; 
lean::dec(x_10);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean::dec(x_7);
return x_19;
}
}
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___spec__2(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_21 = lean::cnstr_get(x_4, 3);
lean::inc(x_21);
x_22 = l_Lean_FileMap_toPosition___main(x_21, x_8);
lean::dec(x_21);
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
lean::dec(x_22);
x_24 = lean::nat_dec_le(x_1, x_23);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Term_letEqns___elambda__1___spec__1___closed__1;
x_26 = l_Lean_Parser_ParserState_mkError(x_5, x_25);
x_9 = x_26;
goto block_20;
}
else
{
x_9 = x_5;
goto block_20;
}
block_20:
{
obj* x_10; 
x_10 = lean::cnstr_get(x_9, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
lean::inc(x_4);
x_11 = l_Lean_Parser_Term_equation___elambda__1(x_3, x_4, x_9);
x_12 = lean::cnstr_get(x_11, 3);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; uint8 x_14; 
lean::dec(x_7);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
x_14 = lean::nat_dec_eq(x_8, x_13);
lean::dec(x_13);
lean::dec(x_8);
if (x_14 == 0)
{
x_5 = x_11;
goto _start;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_4);
x_16 = l_Lean_Parser_manyAux___main___closed__1;
x_17 = l_Lean_Parser_ParserState_mkError(x_11, x_16);
return x_17;
}
}
else
{
obj* x_18; 
lean::dec(x_12);
lean::dec(x_4);
x_18 = l_Lean_Parser_ParserState_restore(x_11, x_7, x_8);
lean::dec(x_7);
return x_18;
}
}
else
{
obj* x_19; 
lean::dec(x_10);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParserState_restore(x_9, x_7, x_8);
lean::dec(x_7);
return x_19;
}
}
}
}
obj* _init_l_Lean_Parser_Command_declValEqns___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Term_letEqns___closed__2;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_declValEqns___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_declValEqns___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declValEqns___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_declValEqns___closed__1;
x_2 = l_Lean_Parser_Command_declValEqns___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declValEqns() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_declValEqns___closed__3;
return x_1;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__1(x_1, x_6, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___elambda__1___spec__2(x_1, x_6, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Command_declValEqns___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Command_declValEqns___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___spec__1(x_1, x_6, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_2);
lean::dec(x_2);
x_7 = l_Lean_Parser_manyAux___main___at_Lean_Parser_Command_declValEqns___spec__2(x_1, x_6, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_Command_declVal___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::inc(x_2);
x_7 = l_Lean_Parser_Command_declValSimple___elambda__1___rarg(x_2, x_3);
x_8 = lean::cnstr_get(x_7, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_9; uint8 x_10; 
lean::dec(x_8);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
x_10 = lean::nat_dec_eq(x_9, x_6);
lean::dec(x_9);
if (x_10 == 0)
{
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_11; obj* x_12; 
x_11 = l_Lean_Parser_ParserState_restore(x_7, x_5, x_6);
lean::dec(x_5);
x_12 = l_Lean_Parser_Command_declValEqns___elambda__1(x_1, x_2, x_11);
return x_12;
}
}
}
}
obj* _init_l_Lean_Parser_Command_declVal___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_Command_declValSimple;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Command_declValEqns;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_orelseInfo(x_2, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Command_declVal___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_declVal___elambda__1___boxed), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_declVal___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_declVal___closed__1;
x_2 = l_Lean_Parser_Command_declVal___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_declVal() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_declVal___closed__3;
return x_1;
}
}
obj* l_Lean_Parser_Command_declVal___elambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Command_declVal___elambda__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_Command_def___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("def");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_def___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_def___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_def___elambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("def ");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_def___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_def___elambda__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_def___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_2 = l_Lean_Parser_Command_def___elambda__1___closed__4;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_def___elambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_def___elambda__1___closed__5;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_def___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Command_def___elambda__1___closed__4;
x_7 = l_Lean_Parser_Command_def___elambda__1___closed__6;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; 
lean::inc(x_2);
x_10 = l_Lean_Parser_Command_declId___elambda__1(x_1, x_2, x_8);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
lean::inc(x_2);
lean::inc(x_1);
x_12 = l_Lean_Parser_Command_optDeclSig___elambda__1(x_1, x_2, x_10);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = l_Lean_Parser_Command_declVal___elambda__1(x_1, x_2, x_12);
lean::dec(x_1);
x_15 = l_Lean_Parser_Command_def___elambda__1___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_5);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_1);
x_17 = l_Lean_Parser_Command_def___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_12, x_17, x_5);
return x_18;
}
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_1);
x_19 = l_Lean_Parser_Command_def___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_10, x_19, x_5);
return x_20;
}
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_9);
lean::dec(x_2);
lean::dec(x_1);
x_21 = l_Lean_Parser_Command_def___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_8, x_21, x_5);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_Command_def___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Command_def___elambda__1___closed__4;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_def___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_Command_optDeclSig;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Command_declVal;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Command_def___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_Command_declId;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Command_def___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_Command_def___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_def___closed__1;
x_2 = l_Lean_Parser_Command_def___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_def___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_def___closed__4;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_def___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_def___elambda__1), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_def___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_def___closed__5;
x_2 = l_Lean_Parser_Command_def___closed__6;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_def() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_def___closed__7;
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_theorem___elambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("theorem");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_theorem___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2;
x_2 = l_Lean_Parser_Command_theorem___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_theorem___elambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("theorem ");
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_theorem___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_theorem___elambda__1___closed__3;
x_2 = l_String_trim(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_theorem___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_symbolFn___rarg___closed__1;
x_2 = l_Lean_Parser_Command_theorem___elambda__1___closed__4;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_theorem___elambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_theorem___elambda__1___closed__5;
x_2 = l_Char_HasRepr___closed__1;
x_3 = lean::string_append(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Command_theorem___elambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_Command_theorem___elambda__1___closed__4;
x_7 = l_Lean_Parser_Command_theorem___elambda__1___closed__6;
lean::inc(x_2);
x_8 = l_Lean_Parser_symbolFnAux(x_6, x_7, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; 
lean::inc(x_2);
x_10 = l_Lean_Parser_Command_declId___elambda__1(x_1, x_2, x_8);
x_11 = lean::cnstr_get(x_10, 3);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
lean::inc(x_2);
lean::inc(x_1);
x_12 = l_Lean_Parser_Command_declSig___elambda__1(x_1, x_2, x_10);
x_13 = lean::cnstr_get(x_12, 3);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = l_Lean_Parser_Command_declVal___elambda__1(x_1, x_2, x_12);
lean::dec(x_1);
x_15 = l_Lean_Parser_Command_theorem___elambda__1___closed__2;
x_16 = l_Lean_Parser_ParserState_mkNode(x_14, x_15, x_5);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_1);
x_17 = l_Lean_Parser_Command_theorem___elambda__1___closed__2;
x_18 = l_Lean_Parser_ParserState_mkNode(x_12, x_17, x_5);
return x_18;
}
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_1);
x_19 = l_Lean_Parser_Command_theorem___elambda__1___closed__2;
x_20 = l_Lean_Parser_ParserState_mkNode(x_10, x_19, x_5);
return x_20;
}
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_9);
lean::dec(x_2);
lean::dec(x_1);
x_21 = l_Lean_Parser_Command_theorem___elambda__1___closed__2;
x_22 = l_Lean_Parser_ParserState_mkNode(x_8, x_21, x_5);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_Command_theorem___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_Command_theorem___elambda__1___closed__4;
x_3 = l_Lean_Parser_symbolInfo(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_theorem___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_Command_declSig;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Command_declVal;
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = l_Lean_Parser_andthenInfo(x_2, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Command_theorem___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Parser_Command_declId;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Lean_Parser_Command_theorem___closed__2;
x_4 = l_Lean_Parser_andthenInfo(x_2, x_3);
return x_4;
}
}
obj* _init_l_Lean_Parser_Command_theorem___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_theorem___closed__1;
x_2 = l_Lean_Parser_Command_theorem___closed__3;
x_3 = l_Lean_Parser_andthenInfo(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_theorem___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_Command_theorem___closed__4;
x_2 = l_Lean_Parser_nodeInfo(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Command_theorem___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Command_theorem___elambda__1), 3, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Command_theorem___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_Command_theorem___closed__5;
x_2 = l_Lean_Parser_Command_theorem___closed__6;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_Command_theorem() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Command_theorem___closed__7;
return x_1;
}
}
obj* initialize_init_lean_parser_term(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_command(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_term(w);
if (io_result_is_error(w)) return w;
w = l_Lean_Parser_mkBuiltinParsingTablesRef(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_builtinCommandParsingTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_Parser_builtinCommandParsingTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "builtinCommandParsingTable"), l_Lean_Parser_builtinCommandParsingTable);
l_Lean_Parser_regBuiltinCommandParserAttr___closed__1 = _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__1();
lean::mark_persistent(l_Lean_Parser_regBuiltinCommandParserAttr___closed__1);
l_Lean_Parser_regBuiltinCommandParserAttr___closed__2 = _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__2();
lean::mark_persistent(l_Lean_Parser_regBuiltinCommandParserAttr___closed__2);
l_Lean_Parser_regBuiltinCommandParserAttr___closed__3 = _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__3();
lean::mark_persistent(l_Lean_Parser_regBuiltinCommandParserAttr___closed__3);
l_Lean_Parser_regBuiltinCommandParserAttr___closed__4 = _init_l_Lean_Parser_regBuiltinCommandParserAttr___closed__4();
lean::mark_persistent(l_Lean_Parser_regBuiltinCommandParserAttr___closed__4);
w = l_Lean_Parser_regBuiltinCommandParserAttr(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_commandParserFn___rarg___closed__1 = _init_l_Lean_Parser_commandParserFn___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_commandParserFn___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "commandParserFn"), 1, l_Lean_Parser_commandParserFn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "commandParser"), 1, l_Lean_Parser_commandParser);
l_Lean_Parser_Command_commentBody___closed__1 = _init_l_Lean_Parser_Command_commentBody___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_commentBody___closed__1);
l_Lean_Parser_Command_commentBody___closed__2 = _init_l_Lean_Parser_Command_commentBody___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_commentBody___closed__2);
l_Lean_Parser_Command_commentBody = _init_l_Lean_Parser_Command_commentBody();
lean::mark_persistent(l_Lean_Parser_Command_commentBody);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "commentBody"), l_Lean_Parser_Command_commentBody);
l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__1);
l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__2);
l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__3);
l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__4);
l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__5);
l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__6 = _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__6();
lean::mark_persistent(l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__6);
l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__7 = _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__7();
lean::mark_persistent(l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__7);
l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__8 = _init_l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__8();
lean::mark_persistent(l_Lean_Parser_Command_docComment___elambda__1___rarg___closed__8);
l_Lean_Parser_Command_docComment___closed__1 = _init_l_Lean_Parser_Command_docComment___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_docComment___closed__1);
l_Lean_Parser_Command_docComment___closed__2 = _init_l_Lean_Parser_Command_docComment___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_docComment___closed__2);
l_Lean_Parser_Command_docComment___closed__3 = _init_l_Lean_Parser_Command_docComment___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_docComment___closed__3);
l_Lean_Parser_Command_docComment___closed__4 = _init_l_Lean_Parser_Command_docComment___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_docComment___closed__4);
l_Lean_Parser_Command_docComment___closed__5 = _init_l_Lean_Parser_Command_docComment___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_docComment___closed__5);
l_Lean_Parser_Command_docComment = _init_l_Lean_Parser_Command_docComment();
lean::mark_persistent(l_Lean_Parser_Command_docComment);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "docComment"), l_Lean_Parser_Command_docComment);
l_Lean_Parser_Command_attrArg___closed__1 = _init_l_Lean_Parser_Command_attrArg___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_attrArg___closed__1);
l_Lean_Parser_Command_attrArg___closed__2 = _init_l_Lean_Parser_Command_attrArg___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_attrArg___closed__2);
l_Lean_Parser_Command_attrArg___closed__3 = _init_l_Lean_Parser_Command_attrArg___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_attrArg___closed__3);
l_Lean_Parser_Command_attrArg___closed__4 = _init_l_Lean_Parser_Command_attrArg___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_attrArg___closed__4);
l_Lean_Parser_Command_attrArg = _init_l_Lean_Parser_Command_attrArg();
lean::mark_persistent(l_Lean_Parser_Command_attrArg);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "attrArg"), l_Lean_Parser_Command_attrArg);
l_Lean_Parser_Command_attrInstance___elambda__1___closed__1 = _init_l_Lean_Parser_Command_attrInstance___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_attrInstance___elambda__1___closed__1);
l_Lean_Parser_Command_attrInstance___elambda__1___closed__2 = _init_l_Lean_Parser_Command_attrInstance___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_attrInstance___elambda__1___closed__2);
l_Lean_Parser_Command_attrInstance___closed__1 = _init_l_Lean_Parser_Command_attrInstance___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_attrInstance___closed__1);
l_Lean_Parser_Command_attrInstance___closed__2 = _init_l_Lean_Parser_Command_attrInstance___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_attrInstance___closed__2);
l_Lean_Parser_Command_attrInstance___closed__3 = _init_l_Lean_Parser_Command_attrInstance___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_attrInstance___closed__3);
l_Lean_Parser_Command_attrInstance___closed__4 = _init_l_Lean_Parser_Command_attrInstance___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_attrInstance___closed__4);
l_Lean_Parser_Command_attrInstance___closed__5 = _init_l_Lean_Parser_Command_attrInstance___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_attrInstance___closed__5);
l_Lean_Parser_Command_attrInstance = _init_l_Lean_Parser_Command_attrInstance();
lean::mark_persistent(l_Lean_Parser_Command_attrInstance);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "attrInstance"), l_Lean_Parser_Command_attrInstance);
l_Lean_Parser_Command_attributes___elambda__1___closed__1 = _init_l_Lean_Parser_Command_attributes___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_attributes___elambda__1___closed__1);
l_Lean_Parser_Command_attributes___elambda__1___closed__2 = _init_l_Lean_Parser_Command_attributes___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_attributes___elambda__1___closed__2);
l_Lean_Parser_Command_attributes___elambda__1___closed__3 = _init_l_Lean_Parser_Command_attributes___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_attributes___elambda__1___closed__3);
l_Lean_Parser_Command_attributes___elambda__1___closed__4 = _init_l_Lean_Parser_Command_attributes___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_attributes___elambda__1___closed__4);
l_Lean_Parser_Command_attributes___elambda__1___closed__5 = _init_l_Lean_Parser_Command_attributes___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_attributes___elambda__1___closed__5);
l_Lean_Parser_Command_attributes___elambda__1___closed__6 = _init_l_Lean_Parser_Command_attributes___elambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_Command_attributes___elambda__1___closed__6);
l_Lean_Parser_Command_attributes___closed__1 = _init_l_Lean_Parser_Command_attributes___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_attributes___closed__1);
l_Lean_Parser_Command_attributes___closed__2 = _init_l_Lean_Parser_Command_attributes___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_attributes___closed__2);
l_Lean_Parser_Command_attributes___closed__3 = _init_l_Lean_Parser_Command_attributes___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_attributes___closed__3);
l_Lean_Parser_Command_attributes___closed__4 = _init_l_Lean_Parser_Command_attributes___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_attributes___closed__4);
l_Lean_Parser_Command_attributes___closed__5 = _init_l_Lean_Parser_Command_attributes___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_attributes___closed__5);
l_Lean_Parser_Command_attributes___closed__6 = _init_l_Lean_Parser_Command_attributes___closed__6();
lean::mark_persistent(l_Lean_Parser_Command_attributes___closed__6);
l_Lean_Parser_Command_attributes___closed__7 = _init_l_Lean_Parser_Command_attributes___closed__7();
lean::mark_persistent(l_Lean_Parser_Command_attributes___closed__7);
l_Lean_Parser_Command_attributes = _init_l_Lean_Parser_Command_attributes();
lean::mark_persistent(l_Lean_Parser_Command_attributes);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "attributes"), l_Lean_Parser_Command_attributes);
l_Lean_Parser_Command_private___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Command_private___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_private___elambda__1___rarg___closed__1);
l_Lean_Parser_Command_private___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Command_private___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_private___elambda__1___rarg___closed__2);
l_Lean_Parser_Command_private___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Command_private___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_private___elambda__1___rarg___closed__3);
l_Lean_Parser_Command_private___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Command_private___elambda__1___rarg___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_private___elambda__1___rarg___closed__4);
l_Lean_Parser_Command_private___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Command_private___elambda__1___rarg___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_private___elambda__1___rarg___closed__5);
l_Lean_Parser_Command_private___closed__1 = _init_l_Lean_Parser_Command_private___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_private___closed__1);
l_Lean_Parser_Command_private___closed__2 = _init_l_Lean_Parser_Command_private___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_private___closed__2);
l_Lean_Parser_Command_private___closed__3 = _init_l_Lean_Parser_Command_private___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_private___closed__3);
l_Lean_Parser_Command_private___closed__4 = _init_l_Lean_Parser_Command_private___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_private___closed__4);
l_Lean_Parser_Command_private = _init_l_Lean_Parser_Command_private();
lean::mark_persistent(l_Lean_Parser_Command_private);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "private"), l_Lean_Parser_Command_private);
l_Lean_Parser_Command_protected___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Command_protected___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_protected___elambda__1___rarg___closed__1);
l_Lean_Parser_Command_protected___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Command_protected___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_protected___elambda__1___rarg___closed__2);
l_Lean_Parser_Command_protected___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Command_protected___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_protected___elambda__1___rarg___closed__3);
l_Lean_Parser_Command_protected___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Command_protected___elambda__1___rarg___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_protected___elambda__1___rarg___closed__4);
l_Lean_Parser_Command_protected___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Command_protected___elambda__1___rarg___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_protected___elambda__1___rarg___closed__5);
l_Lean_Parser_Command_protected___closed__1 = _init_l_Lean_Parser_Command_protected___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_protected___closed__1);
l_Lean_Parser_Command_protected___closed__2 = _init_l_Lean_Parser_Command_protected___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_protected___closed__2);
l_Lean_Parser_Command_protected___closed__3 = _init_l_Lean_Parser_Command_protected___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_protected___closed__3);
l_Lean_Parser_Command_protected___closed__4 = _init_l_Lean_Parser_Command_protected___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_protected___closed__4);
l_Lean_Parser_Command_protected = _init_l_Lean_Parser_Command_protected();
lean::mark_persistent(l_Lean_Parser_Command_protected);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "protected"), l_Lean_Parser_Command_protected);
l_Lean_Parser_Command_visibility___closed__1 = _init_l_Lean_Parser_Command_visibility___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_visibility___closed__1);
l_Lean_Parser_Command_visibility___closed__2 = _init_l_Lean_Parser_Command_visibility___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_visibility___closed__2);
l_Lean_Parser_Command_visibility___closed__3 = _init_l_Lean_Parser_Command_visibility___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_visibility___closed__3);
l_Lean_Parser_Command_visibility = _init_l_Lean_Parser_Command_visibility();
lean::mark_persistent(l_Lean_Parser_Command_visibility);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "visibility"), l_Lean_Parser_Command_visibility);
l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__1);
l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__2);
l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__3);
l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__4);
l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_noncomputable___elambda__1___rarg___closed__5);
l_Lean_Parser_Command_noncomputable___closed__1 = _init_l_Lean_Parser_Command_noncomputable___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_noncomputable___closed__1);
l_Lean_Parser_Command_noncomputable___closed__2 = _init_l_Lean_Parser_Command_noncomputable___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_noncomputable___closed__2);
l_Lean_Parser_Command_noncomputable___closed__3 = _init_l_Lean_Parser_Command_noncomputable___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_noncomputable___closed__3);
l_Lean_Parser_Command_noncomputable___closed__4 = _init_l_Lean_Parser_Command_noncomputable___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_noncomputable___closed__4);
l_Lean_Parser_Command_noncomputable = _init_l_Lean_Parser_Command_noncomputable();
lean::mark_persistent(l_Lean_Parser_Command_noncomputable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "noncomputable"), l_Lean_Parser_Command_noncomputable);
l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__1);
l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__2);
l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__3 = _init_l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__3);
l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__4 = _init_l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__4);
l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__5 = _init_l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_unsafe___elambda__1___rarg___closed__5);
l_Lean_Parser_Command_unsafe___closed__1 = _init_l_Lean_Parser_Command_unsafe___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_unsafe___closed__1);
l_Lean_Parser_Command_unsafe___closed__2 = _init_l_Lean_Parser_Command_unsafe___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_unsafe___closed__2);
l_Lean_Parser_Command_unsafe___closed__3 = _init_l_Lean_Parser_Command_unsafe___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_unsafe___closed__3);
l_Lean_Parser_Command_unsafe___closed__4 = _init_l_Lean_Parser_Command_unsafe___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_unsafe___closed__4);
l_Lean_Parser_Command_unsafe = _init_l_Lean_Parser_Command_unsafe();
lean::mark_persistent(l_Lean_Parser_Command_unsafe);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "unsafe"), l_Lean_Parser_Command_unsafe);
l_Lean_Parser_Command_declModifiers___elambda__1___closed__1 = _init_l_Lean_Parser_Command_declModifiers___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___elambda__1___closed__1);
l_Lean_Parser_Command_declModifiers___elambda__1___closed__2 = _init_l_Lean_Parser_Command_declModifiers___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___elambda__1___closed__2);
l_Lean_Parser_Command_declModifiers___closed__1 = _init_l_Lean_Parser_Command_declModifiers___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__1);
l_Lean_Parser_Command_declModifiers___closed__2 = _init_l_Lean_Parser_Command_declModifiers___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__2);
l_Lean_Parser_Command_declModifiers___closed__3 = _init_l_Lean_Parser_Command_declModifiers___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__3);
l_Lean_Parser_Command_declModifiers___closed__4 = _init_l_Lean_Parser_Command_declModifiers___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__4);
l_Lean_Parser_Command_declModifiers___closed__5 = _init_l_Lean_Parser_Command_declModifiers___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__5);
l_Lean_Parser_Command_declModifiers___closed__6 = _init_l_Lean_Parser_Command_declModifiers___closed__6();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__6);
l_Lean_Parser_Command_declModifiers___closed__7 = _init_l_Lean_Parser_Command_declModifiers___closed__7();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__7);
l_Lean_Parser_Command_declModifiers___closed__8 = _init_l_Lean_Parser_Command_declModifiers___closed__8();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__8);
l_Lean_Parser_Command_declModifiers___closed__9 = _init_l_Lean_Parser_Command_declModifiers___closed__9();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__9);
l_Lean_Parser_Command_declModifiers___closed__10 = _init_l_Lean_Parser_Command_declModifiers___closed__10();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__10);
l_Lean_Parser_Command_declModifiers___closed__11 = _init_l_Lean_Parser_Command_declModifiers___closed__11();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__11);
l_Lean_Parser_Command_declModifiers___closed__12 = _init_l_Lean_Parser_Command_declModifiers___closed__12();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers___closed__12);
l_Lean_Parser_Command_declModifiers = _init_l_Lean_Parser_Command_declModifiers();
lean::mark_persistent(l_Lean_Parser_Command_declModifiers);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "declModifiers"), l_Lean_Parser_Command_declModifiers);
l_Lean_Parser_Command_declId___elambda__1___closed__1 = _init_l_Lean_Parser_Command_declId___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declId___elambda__1___closed__1);
l_Lean_Parser_Command_declId___elambda__1___closed__2 = _init_l_Lean_Parser_Command_declId___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declId___elambda__1___closed__2);
l_Lean_Parser_Command_declId___closed__1 = _init_l_Lean_Parser_Command_declId___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declId___closed__1);
l_Lean_Parser_Command_declId___closed__2 = _init_l_Lean_Parser_Command_declId___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declId___closed__2);
l_Lean_Parser_Command_declId___closed__3 = _init_l_Lean_Parser_Command_declId___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_declId___closed__3);
l_Lean_Parser_Command_declId___closed__4 = _init_l_Lean_Parser_Command_declId___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_declId___closed__4);
l_Lean_Parser_Command_declId___closed__5 = _init_l_Lean_Parser_Command_declId___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_declId___closed__5);
l_Lean_Parser_Command_declId___closed__6 = _init_l_Lean_Parser_Command_declId___closed__6();
lean::mark_persistent(l_Lean_Parser_Command_declId___closed__6);
l_Lean_Parser_Command_declId___closed__7 = _init_l_Lean_Parser_Command_declId___closed__7();
lean::mark_persistent(l_Lean_Parser_Command_declId___closed__7);
l_Lean_Parser_Command_declId___closed__8 = _init_l_Lean_Parser_Command_declId___closed__8();
lean::mark_persistent(l_Lean_Parser_Command_declId___closed__8);
l_Lean_Parser_Command_declId = _init_l_Lean_Parser_Command_declId();
lean::mark_persistent(l_Lean_Parser_Command_declId);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "declId"), l_Lean_Parser_Command_declId);
l_Lean_Parser_Command_declSig___elambda__1___closed__1 = _init_l_Lean_Parser_Command_declSig___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declSig___elambda__1___closed__1);
l_Lean_Parser_Command_declSig___elambda__1___closed__2 = _init_l_Lean_Parser_Command_declSig___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declSig___elambda__1___closed__2);
l_Lean_Parser_Command_declSig___closed__1 = _init_l_Lean_Parser_Command_declSig___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declSig___closed__1);
l_Lean_Parser_Command_declSig___closed__2 = _init_l_Lean_Parser_Command_declSig___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declSig___closed__2);
l_Lean_Parser_Command_declSig___closed__3 = _init_l_Lean_Parser_Command_declSig___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_declSig___closed__3);
l_Lean_Parser_Command_declSig___closed__4 = _init_l_Lean_Parser_Command_declSig___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_declSig___closed__4);
l_Lean_Parser_Command_declSig = _init_l_Lean_Parser_Command_declSig();
lean::mark_persistent(l_Lean_Parser_Command_declSig);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "declSig"), l_Lean_Parser_Command_declSig);
l_Lean_Parser_Command_optDeclSig___elambda__1___closed__1 = _init_l_Lean_Parser_Command_optDeclSig___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_optDeclSig___elambda__1___closed__1);
l_Lean_Parser_Command_optDeclSig___elambda__1___closed__2 = _init_l_Lean_Parser_Command_optDeclSig___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_optDeclSig___elambda__1___closed__2);
l_Lean_Parser_Command_optDeclSig___closed__1 = _init_l_Lean_Parser_Command_optDeclSig___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_optDeclSig___closed__1);
l_Lean_Parser_Command_optDeclSig___closed__2 = _init_l_Lean_Parser_Command_optDeclSig___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_optDeclSig___closed__2);
l_Lean_Parser_Command_optDeclSig___closed__3 = _init_l_Lean_Parser_Command_optDeclSig___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_optDeclSig___closed__3);
l_Lean_Parser_Command_optDeclSig___closed__4 = _init_l_Lean_Parser_Command_optDeclSig___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_optDeclSig___closed__4);
l_Lean_Parser_Command_optDeclSig = _init_l_Lean_Parser_Command_optDeclSig();
lean::mark_persistent(l_Lean_Parser_Command_optDeclSig);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "optDeclSig"), l_Lean_Parser_Command_optDeclSig);
l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__1 = _init_l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__1);
l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__2 = _init_l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declValSimple___elambda__1___rarg___closed__2);
l_Lean_Parser_Command_declValSimple___closed__1 = _init_l_Lean_Parser_Command_declValSimple___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declValSimple___closed__1);
l_Lean_Parser_Command_declValSimple___closed__2 = _init_l_Lean_Parser_Command_declValSimple___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declValSimple___closed__2);
l_Lean_Parser_Command_declValSimple = _init_l_Lean_Parser_Command_declValSimple();
lean::mark_persistent(l_Lean_Parser_Command_declValSimple);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "declValSimple"), l_Lean_Parser_Command_declValSimple);
l_Lean_Parser_Command_declValEqns___elambda__1___closed__1 = _init_l_Lean_Parser_Command_declValEqns___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declValEqns___elambda__1___closed__1);
l_Lean_Parser_Command_declValEqns___elambda__1___closed__2 = _init_l_Lean_Parser_Command_declValEqns___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declValEqns___elambda__1___closed__2);
l_Lean_Parser_Command_declValEqns___closed__1 = _init_l_Lean_Parser_Command_declValEqns___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declValEqns___closed__1);
l_Lean_Parser_Command_declValEqns___closed__2 = _init_l_Lean_Parser_Command_declValEqns___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declValEqns___closed__2);
l_Lean_Parser_Command_declValEqns___closed__3 = _init_l_Lean_Parser_Command_declValEqns___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_declValEqns___closed__3);
l_Lean_Parser_Command_declValEqns = _init_l_Lean_Parser_Command_declValEqns();
lean::mark_persistent(l_Lean_Parser_Command_declValEqns);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "declValEqns"), l_Lean_Parser_Command_declValEqns);
l_Lean_Parser_Command_declVal___closed__1 = _init_l_Lean_Parser_Command_declVal___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_declVal___closed__1);
l_Lean_Parser_Command_declVal___closed__2 = _init_l_Lean_Parser_Command_declVal___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_declVal___closed__2);
l_Lean_Parser_Command_declVal___closed__3 = _init_l_Lean_Parser_Command_declVal___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_declVal___closed__3);
l_Lean_Parser_Command_declVal = _init_l_Lean_Parser_Command_declVal();
lean::mark_persistent(l_Lean_Parser_Command_declVal);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "declVal"), l_Lean_Parser_Command_declVal);
l_Lean_Parser_Command_def___elambda__1___closed__1 = _init_l_Lean_Parser_Command_def___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_def___elambda__1___closed__1);
l_Lean_Parser_Command_def___elambda__1___closed__2 = _init_l_Lean_Parser_Command_def___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_def___elambda__1___closed__2);
l_Lean_Parser_Command_def___elambda__1___closed__3 = _init_l_Lean_Parser_Command_def___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_def___elambda__1___closed__3);
l_Lean_Parser_Command_def___elambda__1___closed__4 = _init_l_Lean_Parser_Command_def___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_def___elambda__1___closed__4);
l_Lean_Parser_Command_def___elambda__1___closed__5 = _init_l_Lean_Parser_Command_def___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_def___elambda__1___closed__5);
l_Lean_Parser_Command_def___elambda__1___closed__6 = _init_l_Lean_Parser_Command_def___elambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_Command_def___elambda__1___closed__6);
l_Lean_Parser_Command_def___closed__1 = _init_l_Lean_Parser_Command_def___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_def___closed__1);
l_Lean_Parser_Command_def___closed__2 = _init_l_Lean_Parser_Command_def___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_def___closed__2);
l_Lean_Parser_Command_def___closed__3 = _init_l_Lean_Parser_Command_def___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_def___closed__3);
l_Lean_Parser_Command_def___closed__4 = _init_l_Lean_Parser_Command_def___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_def___closed__4);
l_Lean_Parser_Command_def___closed__5 = _init_l_Lean_Parser_Command_def___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_def___closed__5);
l_Lean_Parser_Command_def___closed__6 = _init_l_Lean_Parser_Command_def___closed__6();
lean::mark_persistent(l_Lean_Parser_Command_def___closed__6);
l_Lean_Parser_Command_def___closed__7 = _init_l_Lean_Parser_Command_def___closed__7();
lean::mark_persistent(l_Lean_Parser_Command_def___closed__7);
l_Lean_Parser_Command_def = _init_l_Lean_Parser_Command_def();
lean::mark_persistent(l_Lean_Parser_Command_def);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "def"), l_Lean_Parser_Command_def);
l_Lean_Parser_Command_theorem___elambda__1___closed__1 = _init_l_Lean_Parser_Command_theorem___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_theorem___elambda__1___closed__1);
l_Lean_Parser_Command_theorem___elambda__1___closed__2 = _init_l_Lean_Parser_Command_theorem___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_theorem___elambda__1___closed__2);
l_Lean_Parser_Command_theorem___elambda__1___closed__3 = _init_l_Lean_Parser_Command_theorem___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_theorem___elambda__1___closed__3);
l_Lean_Parser_Command_theorem___elambda__1___closed__4 = _init_l_Lean_Parser_Command_theorem___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_theorem___elambda__1___closed__4);
l_Lean_Parser_Command_theorem___elambda__1___closed__5 = _init_l_Lean_Parser_Command_theorem___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_theorem___elambda__1___closed__5);
l_Lean_Parser_Command_theorem___elambda__1___closed__6 = _init_l_Lean_Parser_Command_theorem___elambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_Command_theorem___elambda__1___closed__6);
l_Lean_Parser_Command_theorem___closed__1 = _init_l_Lean_Parser_Command_theorem___closed__1();
lean::mark_persistent(l_Lean_Parser_Command_theorem___closed__1);
l_Lean_Parser_Command_theorem___closed__2 = _init_l_Lean_Parser_Command_theorem___closed__2();
lean::mark_persistent(l_Lean_Parser_Command_theorem___closed__2);
l_Lean_Parser_Command_theorem___closed__3 = _init_l_Lean_Parser_Command_theorem___closed__3();
lean::mark_persistent(l_Lean_Parser_Command_theorem___closed__3);
l_Lean_Parser_Command_theorem___closed__4 = _init_l_Lean_Parser_Command_theorem___closed__4();
lean::mark_persistent(l_Lean_Parser_Command_theorem___closed__4);
l_Lean_Parser_Command_theorem___closed__5 = _init_l_Lean_Parser_Command_theorem___closed__5();
lean::mark_persistent(l_Lean_Parser_Command_theorem___closed__5);
l_Lean_Parser_Command_theorem___closed__6 = _init_l_Lean_Parser_Command_theorem___closed__6();
lean::mark_persistent(l_Lean_Parser_Command_theorem___closed__6);
l_Lean_Parser_Command_theorem___closed__7 = _init_l_Lean_Parser_Command_theorem___closed__7();
lean::mark_persistent(l_Lean_Parser_Command_theorem___closed__7);
l_Lean_Parser_Command_theorem = _init_l_Lean_Parser_Command_theorem();
lean::mark_persistent(l_Lean_Parser_Command_theorem);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Parser"), "Command"), "theorem"), l_Lean_Parser_Command_theorem);
return w;
}
