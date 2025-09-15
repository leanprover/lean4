// Lean compiler output
// Module: Lean.DocString.Syntax
// Imports: Init.Prelude Init.Notation Lean.Parser.Types Lean.Syntax Lean.Parser.Extra Lean.Parser.Term Lean.Parser.Term
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
static lean_object* l_Lean_Doc_Syntax_inline__math___closed__1;
lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_display__math___closed__4;
static lean_object* l_Lean_Doc_Syntax_display__math___closed__1;
static lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__3;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__10;
lean_object* l_Lean_Parser_checkColEq(lean_object*);
static lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__3;
static lean_object* l_Lean_Doc_Syntax_emph___closed__7;
static lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__4;
static lean_object* l_Lean_Doc_Syntax_named___closed__2;
static lean_object* l_Lean_Doc_Syntax_url___closed__1;
static lean_object* l_Lean_Doc_Syntax_ol___closed__2;
static lean_object* l_Lean_Doc_Syntax_ul___closed__1;
static lean_object* l_Lean_Doc_Syntax_ol___closed__7;
static lean_object* l_Lean_Doc_Syntax_desc___closed__2;
static lean_object* l_Lean_Doc_Syntax_metadata__block___closed__7;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__0;
extern lean_object* l_Lean_Parser_pushNone;
static lean_object* l_Lean_Doc_Syntax_li___closed__6;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_bold;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_footnote__ref;
static lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__9;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__11;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__9;
static lean_object* l_Lean_Doc_Syntax_flag__off___closed__0;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__9;
static lean_object* l_Lean_Doc_Syntax_text___closed__2;
static lean_object* l_Lean_Doc_Syntax_footnote___closed__2;
static lean_object* l_Lean_Doc_Syntax_para___closed__9;
static lean_object* l_Lean_Doc_Syntax_display__math___closed__0;
static lean_object* l_Lean_Doc_Syntax_arg__num___closed__5;
static lean_object* l_Lean_Doc_Syntax_header___closed__5;
static lean_object* l_Lean_Doc_Syntax_header___closed__9;
static lean_object* l_Lean_Doc_Syntax_dl___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_arg__val;
static lean_object* l_Lean_Doc_Syntax_arg__ident___closed__2;
static lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__0;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__19;
static lean_object* l_Lean_Doc_Syntax_header___closed__4;
static lean_object* l_Lean_Doc_Syntax_directive___closed__0;
static lean_object* l_Lean_Doc_Syntax_code___closed__4;
static lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__9;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__6;
static lean_object* l_Lean_Doc_Syntax_blockquote___closed__2;
static lean_object* l_Lean_Doc_Syntax_header___closed__7;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_named__no__paren;
static lean_object* l_Lean_Doc_Syntax_ref___closed__0;
static lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__6;
static lean_object* l_Lean_Doc_Syntax_footnote___closed__4;
static lean_object* l_Lean_Doc_Syntax_arg__num___closed__4;
static lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__7;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents;
static lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__7;
static lean_object* l_Lean_Doc_Syntax_linebreak___closed__3;
static lean_object* l_Lean_Doc_Syntax_para___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_arg__ident;
static lean_object* l_Lean_Doc_Syntax_emph___closed__9;
static lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___closed__1;
static lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__2;
static lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2;
static lean_object* l_Lean_Doc_Syntax_desc___closed__1;
static lean_object* l_Lean_Doc_Syntax_inline_quot___closed__7;
static lean_object* l_Lean_Doc_Syntax_emph___closed__4;
static lean_object* l_Lean_Doc_Syntax_arg__str___closed__3;
static lean_object* l_Lean_Doc_Syntax_directive___closed__3;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__17;
static lean_object* l_Lean_Doc_Syntax_desc___closed__3;
static lean_object* l_Lean_Doc_Syntax_directive___closed__4;
static lean_object* l_Lean_Doc_Syntax_linebreak___closed__4;
static lean_object* l_Lean_Doc_Syntax_metadata__block___closed__8;
static lean_object* l_Lean_Doc_Syntax_li___closed__3;
static lean_object* l_Lean_Doc_Syntax_dl___closed__4;
static lean_object* l_Lean_Doc_Syntax_linebreak___closed__1;
static lean_object* l_Lean_Doc_Syntax_link__ref___closed__1;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__6;
static lean_object* l_Lean_Doc_Syntax_inline__math___closed__3;
static lean_object* l_Lean_Doc_Syntax_desc___closed__0;
static lean_object* l_Lean_Doc_Syntax_inline_quot___closed__4;
static lean_object* l_Lean_Doc_Syntax_inline_quot___closed__8;
static lean_object* l_Lean_Doc_Syntax_bold___closed__5;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
static lean_object* l_Lean_Doc_Syntax_link__ref___closed__2;
static lean_object* l_Lean_Doc_Syntax_display__math___closed__2;
static lean_object* l_Lean_Doc_Syntax_command___closed__6;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_desc;
static lean_object* l_Lean_Doc_Syntax_arg__num___closed__1;
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__2;
static lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__7;
static lean_object* l_Lean_Doc_Syntax_role___closed__1;
static lean_object* l_Lean_Doc_Syntax_text___closed__0;
static lean_object* l_Lean_Doc_Syntax_metadata__block___closed__0;
static lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__2;
static lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__1;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_flag__on;
static lean_object* l_Lean_Doc_Syntax_link__ref___closed__5;
static lean_object* l_Lean_Doc_Syntax_link__ref___closed__3;
static lean_object* l_Lean_Doc_Syntax_role___closed__3;
static lean_object* l_Lean_Doc_Syntax_block_quot___closed__6;
static lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__7;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_block_quot;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_anon;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__4;
static lean_object* l_Lean_Doc_Syntax_desc___closed__5;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_image;
static lean_object* l_Lean_Doc_Syntax_para___closed__5;
static lean_object* l_Lean_Doc_Syntax_directive___closed__5;
static lean_object* l_Lean_Doc_Syntax_role___closed__10;
static lean_object* l_Lean_Doc_Syntax_image___closed__3;
static lean_object* l_Lean_Doc_Syntax_ol___closed__11;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__14;
static lean_object* l_Lean_Doc_Syntax_flag__on___closed__4;
static lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__1;
static lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__5;
static lean_object* l_Lean_Doc_Syntax_arg__ident___closed__1;
lean_object* l_Lean_Parser_Term_structInstFields(lean_object*);
static lean_object* l_Lean_Doc_Syntax_command___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_metadata__block___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_command;
lean_object* l_Lean_Parser_sepByIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_bold___closed__1;
static lean_object* l_Lean_Doc_Syntax_header___closed__8;
static lean_object* l_Lean_Doc_Syntax_footnote___closed__0;
static lean_object* l_Lean_Doc_Syntax_flag__off___closed__3;
static lean_object* l_Lean_Doc_Syntax_image___closed__1;
static lean_object* l_Lean_Doc_Syntax_ref___closed__1;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_doc__arg_quot;
static lean_object* l_Lean_Doc_Syntax_named___closed__1;
static lean_object* l_Lean_Doc_Syntax_link___closed__5;
static lean_object* l_Lean_Doc_Syntax_arg__str___closed__4;
static lean_object* l_Lean_Doc_Syntax_metadata__block___closed__4;
static lean_object* l_Lean_Doc_Syntax_named___closed__4;
static lean_object* l_Lean_Doc_Syntax_ref___closed__4;
static lean_object* l_Lean_Doc_Syntax_arg__ident___closed__5;
static lean_object* l_Lean_Doc_Syntax_ol___closed__3;
static lean_object* l_Lean_Doc_Syntax_block_quot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_list__item_quot;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__18;
static lean_object* l_Lean_Doc_Syntax_arg__num___closed__0;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__11;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_link;
static lean_object* l_Lean_Doc_Syntax_header___closed__6;
static lean_object* l_Lean_Doc_Syntax_para___closed__1;
static lean_object* l_Lean_Doc_Syntax_desc___closed__8;
lean_object* l_Lean_Parser_Term_structInstFields_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_flag__on___closed__5;
static lean_object* l_Lean_Doc_Syntax_code___closed__1;
static lean_object* l_Lean_Doc_Syntax_command___closed__0;
lean_object* l_Lean_Parser_withPosition(lean_object*);
static lean_object* l_Lean_Doc_Syntax_block_quot___closed__9;
static lean_object* l_Lean_Doc_Syntax_link__ref___closed__6;
extern lean_object* l_Lean_Parser_Term_structInstField;
static lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__2;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__16;
static lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__8;
static lean_object* l_Lean_Doc_Syntax_block_quot___closed__0;
static lean_object* l_Lean_Doc_Syntax_blockquote___closed__4;
static lean_object* l_Lean_Doc_Syntax_ul___closed__2;
static lean_object* l_Lean_Doc_Syntax_role___closed__9;
static lean_object* l_Lean_Doc_Syntax_command___closed__4;
static lean_object* l_Lean_Doc_Syntax_emph___closed__6;
static lean_object* l_Lean_Doc_Syntax_block_quot___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_ul;
static lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__1;
static lean_object* l_Lean_Doc_Syntax_blockquote___closed__1;
static lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__1;
static lean_object* l_Lean_Doc_Syntax_directive___closed__9;
static lean_object* l_Lean_Doc_Syntax_arg__str___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_blockquote___closed__0;
static lean_object* l_Lean_Doc_Syntax_arg__num___closed__3;
static lean_object* l_Lean_Doc_Syntax_directive___closed__11;
static lean_object* l_Lean_Doc_Syntax_emph___closed__2;
static lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__4;
static lean_object* l_Lean_Doc_Syntax_role___closed__13;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__15;
static lean_object* l_Lean_Doc_Syntax_named___closed__7;
static lean_object* l_Lean_Doc_Syntax_inline__math___closed__4;
static lean_object* l_Lean_Doc_Syntax_role___closed__8;
static lean_object* l_Lean_Doc_Syntax_text___closed__1;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__7;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_li;
static lean_object* l_Lean_Doc_Syntax_command___closed__3;
static lean_object* l_Lean_Doc_Syntax_role___closed__0;
static lean_object* l_Lean_Doc_Syntax_metadata__block___closed__1;
static lean_object* l_Lean_Doc_Syntax_image___closed__4;
static lean_object* l_Lean_Doc_Syntax_anon___closed__2;
static lean_object* l_Lean_Doc_Syntax_header___closed__2;
static lean_object* l_Lean_Doc_Syntax_named___closed__3;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__0;
static lean_object* l_Lean_Doc_Syntax_anon___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_text;
static lean_object* l_Lean_Doc_Syntax_flag__on___closed__2;
static lean_object* l_Lean_Doc_Syntax_dl___closed__1;
static lean_object* l_Lean_Doc_Syntax_link___closed__4;
static lean_object* l_Lean_Doc_Syntax_desc___closed__6;
static lean_object* l_Lean_Doc_Syntax_arg__str___closed__0;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__16;
static lean_object* l_Lean_Doc_Syntax_inline_quot___closed__9;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_named;
static lean_object* l_Lean_Doc_Syntax_role___closed__7;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_role;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__0;
static lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__6;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__5;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__8;
static lean_object* l_Lean_Doc_Syntax_para___closed__8;
static lean_object* l_Lean_Doc_Syntax_code___closed__6;
static lean_object* l_Lean_Doc_Syntax_dl___closed__7;
lean_object* l_Lean_Parser_symbol(lean_object*);
static lean_object* l_Lean_Doc_Syntax_blockquote___closed__5;
static lean_object* l_Lean_Doc_Syntax_ol___closed__4;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_inline;
static lean_object* l_Lean_Doc_Syntax_ol___closed__1;
static lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__6;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__5;
static lean_object* l_Lean_Doc_Syntax_li___closed__0;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__13;
lean_object* l_Lean_Parser_symbol_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__1;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__2;
static lean_object* l_Lean_Doc_Syntax_ol___closed__8;
static lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__0;
static lean_object* l_Lean_Doc_Syntax_url___closed__2;
static lean_object* l_Lean_Doc_Syntax_role___closed__12;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_footnote;
static lean_object* l_Lean_Doc_Syntax_emph___closed__3;
static lean_object* l_Lean_Doc_Syntax_metadata__block___closed__3;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__7;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__3;
static lean_object* l_Lean_Doc_Syntax_arg__str___closed__1;
static lean_object* l_Lean_Doc_Syntax_flag__off___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_code;
static lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__4;
static lean_object* l_Lean_Doc_Syntax_ol___closed__0;
static lean_object* l_Lean_Doc_Syntax_arg__ident___closed__3;
static lean_object* l_Lean_Doc_Syntax_link__ref___closed__4;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__9;
static lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_ref;
static lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__8;
static lean_object* l_Lean_Doc_Syntax_directive___closed__10;
static lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___closed__2;
static lean_object* l_Lean_Doc_Syntax_li___closed__4;
static lean_object* l_Lean_Doc_Syntax_inline_quot___closed__1;
static lean_object* l_Lean_Doc_Syntax_block_quot___closed__8;
static lean_object* l_Lean_Doc_Syntax_image___closed__6;
static lean_object* l_Lean_Doc_Syntax_code___closed__0;
static lean_object* l_Lean_Doc_Syntax_arg__ident___closed__4;
static lean_object* l_Lean_Doc_Syntax_image___closed__2;
static lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__4;
static lean_object* l_Lean_Doc_Syntax_command___closed__7;
static lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__5;
static lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__5;
static lean_object* l_Lean_Doc_Syntax_inline__math___closed__0;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__14;
static lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__0;
static lean_object* l_Lean_Doc_Syntax_directive___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_block;
static lean_object* l_Lean_Doc_Syntax_link___closed__6;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_link__target;
static lean_object* l_Lean_Doc_Syntax_block_quot___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_para;
static lean_object* l_Lean_Doc_Syntax_directive___closed__2;
static lean_object* l_Lean_Doc_Syntax_inline_quot___closed__0;
static lean_object* l_Lean_Doc_Syntax_dl___closed__5;
static lean_object* l_Lean_Doc_Syntax_named___closed__5;
static lean_object* l_Lean_Doc_Syntax_ol___closed__6;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__8;
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__2;
static lean_object* l_Lean_Doc_Syntax_inline_quot___closed__2;
static lean_object* l_Lean_Doc_Syntax_arg__str___closed__6;
static lean_object* l_Lean_Doc_Syntax_role___closed__4;
static lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__3;
static lean_object* l_Lean_Doc_Syntax_desc___closed__7;
static lean_object* l_Lean_Doc_Syntax_display__math___closed__3;
lean_object* l_Lean_Parser_checkColGe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_desc__item_quot;
static lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1;
static lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__2;
static lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__0;
static lean_object* l_Lean_Doc_Syntax_bold___closed__2;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__1;
static lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__5;
static lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__7;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__5;
lean_object* l_Lean_Parser_Term_structInstField_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_emph___closed__0;
static lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__4;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__8;
static lean_object* l_Lean_Doc_Syntax_ul___closed__3;
static lean_object* l_Lean_Doc_Syntax_ref___closed__6;
static lean_object* l_Lean_Doc_Syntax_blockquote___closed__3;
static lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__6;
static lean_object* l_Lean_Doc_Syntax_footnote___closed__6;
static lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__1;
static lean_object* l_Lean_Doc_Syntax_inline_quot___closed__3;
static lean_object* l_Lean_Doc_Syntax_metadata__block___closed__6;
static lean_object* l_Lean_Doc_Syntax_directive___closed__14;
static lean_object* l_Lean_Doc_Syntax_link___closed__1;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_link__ref;
static lean_object* l_Lean_Doc_Syntax_dl___closed__2;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__1;
static lean_object* l_Lean_Doc_Syntax_inline__math___closed__5;
static lean_object* l_Lean_Doc_Syntax_command___closed__1;
static lean_object* l_Lean_Doc_Syntax_ul___closed__4;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_list__item;
static lean_object* l_Lean_Doc_Syntax_block_quot___closed__7;
static lean_object* l_Lean_Doc_Syntax_header___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_header;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__11;
static lean_object* l_Lean_Doc_Syntax_bold___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_dl;
static lean_object* l_Lean_Doc_Syntax_flag__off___closed__4;
static lean_object* l_Lean_Doc_Syntax_linebreak___closed__0;
static lean_object* l_Lean_Doc_Syntax_named___closed__10;
static lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__8;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_arg__val_quot;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__10;
static lean_object* l_Lean_Doc_Syntax_code___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_ol;
static lean_object* l_Lean_Doc_Syntax_footnote___closed__1;
static lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__5;
static lean_object* l_Lean_Doc_Syntax_ol___closed__5;
static lean_object* l_Lean_Doc_Syntax_emph___closed__8;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_codeblock;
static lean_object* l_Lean_Doc_Syntax_li___closed__5;
static lean_object* l_Lean_Doc_Syntax_desc___closed__4;
static lean_object* l_Lean_Doc_Syntax_link___closed__2;
static lean_object* l_Lean_Doc_Syntax_emph___closed__1;
static lean_object* l_Lean_Doc_Syntax_ol___closed__9;
static lean_object* l_Lean_Doc_Syntax_directive___closed__13;
static lean_object* l_Lean_Doc_Syntax_ref___closed__2;
static lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__8;
static lean_object* l_Lean_Doc_Syntax_inline_quot___closed__5;
static lean_object* l_Lean_Doc_Syntax_directive___closed__12;
static lean_object* l_Lean_Doc_Syntax_metadata__block___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_directive;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_inline__math;
static lean_object* l_Lean_Doc_Syntax_ref___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_flag__on___closed__1;
static lean_object* l_Lean_Doc_Syntax_url___closed__0;
static lean_object* l_Lean_Doc_Syntax_inline_quot___closed__6;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_ol___closed__10;
static lean_object* l_Lean_Doc_Syntax_flag__on___closed__3;
static lean_object* l_Lean_Doc_Syntax_block_quot___closed__1;
static lean_object* l_Lean_Doc_Syntax_linebreak___closed__5;
lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_anon___closed__1;
static lean_object* l_Lean_Doc_Syntax_directive___closed__7;
static lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__6;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__12;
static lean_object* l_Lean_Doc_Syntax_url___closed__3;
static lean_object* l_Lean_Doc_Syntax_directive___closed__8;
static lean_object* l_Lean_Doc_Syntax_header___closed__0;
static lean_object* l_Lean_Doc_Syntax_para___closed__6;
static lean_object* l_Lean_Doc_Syntax_ul___closed__6;
static lean_object* l_Lean_Doc_Syntax_link___closed__0;
static lean_object* l_Lean_Doc_Syntax_para___closed__7;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__14;
static lean_object* l_Lean_Doc_Syntax_header___closed__1;
static lean_object* l_Lean_Doc_Syntax_image___closed__7;
static lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__9;
static lean_object* l_Lean_Doc_Syntax_flag__on___closed__0;
static lean_object* l_Lean_Doc_Syntax_display__math___closed__5;
static lean_object* l_Lean_Doc_Syntax_link___closed__7;
static lean_object* l_Lean_Doc_Syntax_bold___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_arg__num;
static lean_object* l_Lean_Doc_Syntax_link__ref___closed__0;
static lean_object* l_Lean_Doc_Syntax_code___closed__2;
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__13;
static lean_object* l_Lean_Doc_Syntax_named___closed__0;
static lean_object* l_Lean_Doc_Syntax_image___closed__0;
static lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__4;
static lean_object* l_Lean_Doc_Syntax_para___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_url;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_linebreak;
static lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__9;
static lean_object* l_Lean_Doc_Syntax_footnote___closed__5;
static lean_object* l_Lean_Doc_Syntax_ul___closed__5;
static lean_object* l_Lean_Doc_Syntax_linebreak___closed__2;
static lean_object* l_Lean_Doc_Syntax_arg__str___closed__7;
static lean_object* l_Lean_Doc_Syntax_role___closed__6;
static lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__4;
static lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadata__block;
static lean_object* l_Lean_Doc_Syntax_arg__str___closed__5;
static lean_object* l_Lean_Doc_Syntax_arg__num___closed__2;
static lean_object* l_Lean_Doc_Syntax_flag__off___closed__2;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__18;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__1;
static lean_object* l_Lean_Doc_Syntax_codeblock___closed__6;
static lean_object* l_Lean_Doc_Syntax_bold___closed__0;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_blockquote;
static lean_object* l_Lean_Doc_Syntax_metadata__block___closed__9;
static lean_object* l_Lean_Doc_Syntax_directive___closed__1;
static lean_object* l_Lean_Doc_Syntax_named___closed__8;
static lean_object* l_Lean_Doc_Syntax_emph___closed__5;
static lean_object* l_Lean_Doc_Syntax_ref___closed__8;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_arg__str;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_flag__off;
static lean_object* l_Lean_Doc_Syntax_link___closed__3;
static lean_object* l_Lean_Doc_Syntax_block_quot___closed__2;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__12;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_desc__item;
static lean_object* l_Lean_Doc_Syntax_li___closed__2;
static lean_object* l_Lean_Doc_Syntax_para___closed__4;
static lean_object* l_Lean_Doc_Syntax_flag__off___closed__1;
static lean_object* l_Lean_Doc_Syntax_bold___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_doc__arg;
static lean_object* l_Lean_Doc_Syntax_ref___closed__7;
static lean_object* l_Lean_Doc_Syntax_role___closed__11;
static lean_object* l_Lean_Doc_Syntax_li___closed__1;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__17;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_inline_quot;
static lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___closed__0;
static lean_object* l_Lean_Doc_Syntax_url___closed__4;
static lean_object* l_Lean_Doc_Syntax_role___closed__5;
static lean_object* l_Lean_Doc_Syntax_code___closed__5;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_link__target_quot;
static lean_object* l_Lean_Doc_Syntax_para___closed__0;
static lean_object* l_Lean_Doc_Syntax_command___closed__2;
static lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_emph;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__10;
static lean_object* l_Lean_Doc_Syntax_named___closed__9;
static lean_object* l_Lean_Doc_Syntax_arg__ident___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_display__math;
static lean_object* l_Lean_Doc_Syntax_dl___closed__3;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__13;
static lean_object* l_Lean_Doc_Syntax_ul___closed__7;
static lean_object* l_Lean_Doc_Syntax_footnote___closed__3;
static lean_object* l_Lean_Doc_Syntax_named___closed__6;
static lean_object* l_Lean_Doc_Syntax_desc___closed__9;
static lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__3;
static lean_object* l_Lean_Doc_Syntax_role___closed__2;
static lean_object* l_Lean_Doc_Syntax_ul___closed__0;
static lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__15;
lean_object* l_Lean_Parser_Term_structInstField_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Doc_Syntax_inline__math___closed__2;
static lean_object* l_Lean_Doc_Syntax_dl___closed__0;
static lean_object* l_Lean_Doc_Syntax_image___closed__5;
static lean_object* l_Lean_Doc_Syntax_ref___closed__5;
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quot", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__3;
x_2 = l_Lean_Doc_Syntax_arg__val_quot___closed__2;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__1;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arg_val", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__3;
x_2 = l_Lean_Doc_Syntax_arg__val_quot___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`(arg_val| ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__9;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Doc_Syntax_arg__val_quot___closed__11;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__13;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_arg__val_quot___closed__12;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__15;
x_2 = l_Lean_Doc_Syntax_arg__val_quot___closed__10;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__16;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__6;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__17;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__val_quot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__18;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Category_arg__val() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__str___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Doc", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__str___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Syntax", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__str___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arg_str", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__str___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__2;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__str___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__str___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__str___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__str___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_arg__str___closed__3;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__str() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__ident___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arg_ident", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__ident___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_arg__ident___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__ident___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__ident___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_arg__ident___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__ident___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_arg__ident___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__ident___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__ident___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_arg__ident___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__ident() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_arg__ident___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__num___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arg_num", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__num___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_arg__num___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__num___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__num___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_arg__num___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__num___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_arg__num___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__num___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__num___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_arg__num___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_arg__num() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_arg__num___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("doc_arg", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__3;
x_2 = l_Lean_Doc_Syntax_doc__arg_quot___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`(doc_arg| ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_doc__arg_quot___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_doc__arg_quot___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Doc_Syntax_doc__arg_quot___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_doc__arg_quot___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_doc__arg_quot___closed__6;
x_2 = l_Lean_Doc_Syntax_doc__arg_quot___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_doc__arg_quot___closed__7;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_doc__arg_quot___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_doc__arg_quot___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_doc__arg_quot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_doc__arg_quot___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Category_doc__arg() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_anon___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("anon", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_anon___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_anon___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_anon___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__12;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_anon___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_anon() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_anon___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("named", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_named___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_named___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__ident___closed__4;
x_2 = l_Lean_Doc_Syntax_named___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_named___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_named___closed__6;
x_2 = l_Lean_Doc_Syntax_named___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__12;
x_2 = l_Lean_Doc_Syntax_named___closed__7;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_named___closed__8;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_named___closed__9;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_named___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_named___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named__no__paren___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("named_no_paren", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named__no__paren___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_named__no__paren___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named__no__paren___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_named___closed__6;
x_2 = l_Lean_Doc_Syntax_arg__ident___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named__no__paren___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__12;
x_2 = l_Lean_Doc_Syntax_named__no__paren___closed__2;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named__no__paren___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_named__no__paren___closed__3;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_named__no__paren___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_named__no__paren() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_named__no__paren___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__on___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("flag_on", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__on___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_flag__on___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__on___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__on___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_flag__on___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__on___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__ident___closed__4;
x_2 = l_Lean_Doc_Syntax_flag__on___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__on___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_flag__on___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_flag__on___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__on() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_flag__on___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__off___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("flag_off", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__off___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_flag__off___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__off___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__off___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_flag__off___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__off___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__ident___closed__4;
x_2 = l_Lean_Doc_Syntax_flag__off___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__off___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_flag__off___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_flag__off___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_flag__off() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_flag__off___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("link_target", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__3;
x_2 = l_Lean_Doc_Syntax_link__target_quot___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`(link_target| ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_link__target_quot___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_link__target_quot___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Doc_Syntax_link__target_quot___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_link__target_quot___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_link__target_quot___closed__6;
x_2 = l_Lean_Doc_Syntax_link__target_quot___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_link__target_quot___closed__7;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_link__target_quot___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_link__target_quot___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__target_quot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_link__target_quot___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Category_link__target() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_url___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("url", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_url___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_url___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_url___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = l_Lean_Doc_Syntax_named___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_url___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_url___closed__2;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_url___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_url___closed__3;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_url___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_url() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_url___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ref___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ref", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ref___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_ref___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ref___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ref___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_ref___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ref___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = l_Lean_Doc_Syntax_ref___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ref___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ref___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_ref___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ref___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ref___closed__6;
x_2 = l_Lean_Doc_Syntax_ref___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ref___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ref___closed__7;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_ref___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ref() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_ref___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inline", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__3;
x_2 = l_Lean_Doc_Syntax_inline_quot___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`(inline| ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_inline_quot___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_inline_quot___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Doc_Syntax_inline_quot___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_inline_quot___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_inline_quot___closed__6;
x_2 = l_Lean_Doc_Syntax_inline_quot___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_inline_quot___closed__7;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_inline_quot___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_inline_quot___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline_quot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_inline_quot___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Category_inline() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_text___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("text", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_text___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_text___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_text___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_text___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_text() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_text___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emph", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_emph___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_emph___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("many", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_emph___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_inline_quot___closed__5;
x_2 = l_Lean_Doc_Syntax_emph___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_emph___closed__6;
x_2 = l_Lean_Doc_Syntax_emph___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ref___closed__6;
x_2 = l_Lean_Doc_Syntax_emph___closed__7;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_emph___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_emph___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_emph() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_emph___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_bold___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bold", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_bold___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_bold___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_bold___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_bold___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_bold___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_bold___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_emph___closed__6;
x_2 = l_Lean_Doc_Syntax_bold___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_bold___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ref___closed__6;
x_2 = l_Lean_Doc_Syntax_bold___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_bold___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_bold___closed__5;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_bold___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_bold() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_bold___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("link", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_link___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("link[", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_link___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_emph___closed__6;
x_2 = l_Lean_Doc_Syntax_link___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ref___closed__6;
x_2 = l_Lean_Doc_Syntax_link___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_link__target_quot___closed__5;
x_2 = l_Lean_Doc_Syntax_link___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_link___closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_link___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_link___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_image___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("image", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_image___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_image___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_image___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("image(", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_image___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_image___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_image___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = l_Lean_Doc_Syntax_image___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_image___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_image___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_image___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_link__target_quot___closed__5;
x_2 = l_Lean_Doc_Syntax_image___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_image___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_image___closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_image___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_image() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_image___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("footnote", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_footnote___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("footnote(", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_footnote___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = l_Lean_Doc_Syntax_footnote___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_footnote___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_footnote___closed__5;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_footnote___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_footnote___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_linebreak___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linebreak", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_linebreak___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_linebreak___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_linebreak___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("line!", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_linebreak___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_linebreak___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_linebreak___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = l_Lean_Doc_Syntax_linebreak___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_linebreak___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_linebreak___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_linebreak___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_linebreak() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_linebreak___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_code___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_code___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_code___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_code___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code(", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_code___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_code___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_code___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = l_Lean_Doc_Syntax_code___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_code___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_code___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_code___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_code___closed__5;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_code___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_code() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_code___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("role", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_role___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("role{", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_role___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__ident___closed__4;
x_2 = l_Lean_Doc_Syntax_role___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_doc__arg_quot___closed__5;
x_2 = l_Lean_Doc_Syntax_emph___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__5;
x_2 = l_Lean_Doc_Syntax_role___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("}", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_role___closed__7;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__8;
x_2 = l_Lean_Doc_Syntax_role___closed__6;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ref___closed__3;
x_2 = l_Lean_Doc_Syntax_role___closed__9;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_emph___closed__6;
x_2 = l_Lean_Doc_Syntax_role___closed__10;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ref___closed__6;
x_2 = l_Lean_Doc_Syntax_role___closed__11;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__12;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_role___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_role() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_role___closed__13;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline__math___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inline_math", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline__math___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_inline__math___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline__math___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\math", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline__math___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_inline__math___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline__math___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_code;
x_2 = l_Lean_Doc_Syntax_inline__math___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline__math___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_inline__math___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_inline__math___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_inline__math() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_inline__math___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_display__math___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("display_math", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_display__math___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_display__math___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_display__math___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\\displaymath", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_display__math___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_display__math___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_display__math___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_code;
x_2 = l_Lean_Doc_Syntax_display__math___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_display__math___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_display__math___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_display__math___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_display__math() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_display__math___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("block", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__3;
x_2 = l_Lean_Doc_Syntax_block_quot___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`(block| ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_block_quot___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_block_quot___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Doc_Syntax_block_quot___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_block_quot___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_block_quot___closed__6;
x_2 = l_Lean_Doc_Syntax_block_quot___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_block_quot___closed__7;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_block_quot___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_block_quot___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_block_quot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_block_quot___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Category_block() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("list_item", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__3;
x_2 = l_Lean_Doc_Syntax_list__item_quot___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`(list_item| ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_list__item_quot___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_list__item_quot___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Doc_Syntax_list__item_quot___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_list__item_quot___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_list__item_quot___closed__6;
x_2 = l_Lean_Doc_Syntax_list__item_quot___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_list__item_quot___closed__7;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_list__item_quot___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_list__item_quot___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_list__item_quot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_list__item_quot___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Category_list__item() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_li___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("li", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_li___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_li___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_li___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_li___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_li___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_li___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_block_quot___closed__5;
x_2 = l_Lean_Doc_Syntax_emph___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_li___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_li___closed__4;
x_2 = l_Lean_Doc_Syntax_li___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_li___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_li___closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_li___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_li() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_li___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("desc_item", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__3;
x_2 = l_Lean_Doc_Syntax_desc__item_quot___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`(desc_item| ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_desc__item_quot___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_desc__item_quot___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Doc_Syntax_desc__item_quot___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_desc__item_quot___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_desc__item_quot___closed__6;
x_2 = l_Lean_Doc_Syntax_desc__item_quot___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_desc__item_quot___closed__7;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_desc__item_quot___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_desc__item_quot___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__4;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc__item_quot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_desc__item_quot___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Category_desc__item() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("desc", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_desc___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_desc___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_emph___closed__6;
x_2 = l_Lean_Doc_Syntax_desc___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=>", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_desc___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_desc___closed__6;
x_2 = l_Lean_Doc_Syntax_desc___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_li___closed__4;
x_2 = l_Lean_Doc_Syntax_desc___closed__7;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_desc___closed__8;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_desc___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_desc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_desc___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("para", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_para___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("para[", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_para___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("many1", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_para___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_inline_quot___closed__5;
x_2 = l_Lean_Doc_Syntax_para___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_para___closed__6;
x_2 = l_Lean_Doc_Syntax_para___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ref___closed__6;
x_2 = l_Lean_Doc_Syntax_para___closed__7;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_para___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_para___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_para() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_para___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ul___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ul", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ul___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_ul___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ul___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ul{", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ul___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_ul___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ul___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_list__item_quot___closed__5;
x_2 = l_Lean_Doc_Syntax_emph___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ul___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ul___closed__4;
x_2 = l_Lean_Doc_Syntax_ul___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ul___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__8;
x_2 = l_Lean_Doc_Syntax_ul___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ul___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ul___closed__6;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_ul___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ul() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_ul___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_dl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dl", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_dl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_dl___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_dl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dl{", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_dl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_dl___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_dl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_desc__item_quot___closed__5;
x_2 = l_Lean_Doc_Syntax_emph___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_dl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_dl___closed__4;
x_2 = l_Lean_Doc_Syntax_dl___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_dl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__8;
x_2 = l_Lean_Doc_Syntax_dl___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_dl___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_dl___closed__6;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_dl___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_dl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_dl___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ol", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_ol___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ol(", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_ol___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__num___closed__4;
x_2 = l_Lean_Doc_Syntax_ol___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_ol___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_ol___closed__6;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ol___closed__7;
x_2 = l_Lean_Doc_Syntax_ol___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ul___closed__4;
x_2 = l_Lean_Doc_Syntax_ol___closed__8;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__8;
x_2 = l_Lean_Doc_Syntax_ol___closed__9;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ol___closed__10;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_ol___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_ol() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_ol___closed__11;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("codeblock", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_codeblock___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("```", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_codeblock___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optional", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_codeblock___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__5;
x_2 = l_Lean_Doc_Syntax_arg__ident___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_codeblock___closed__6;
x_2 = l_Lean_Doc_Syntax_codeblock___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_codeblock___closed__7;
x_2 = l_Lean_Doc_Syntax_codeblock___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("|", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_codeblock___closed__9;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_codeblock___closed__10;
x_2 = l_Lean_Doc_Syntax_codeblock___closed__8;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = l_Lean_Doc_Syntax_codeblock___closed__11;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_codeblock___closed__3;
x_2 = l_Lean_Doc_Syntax_codeblock___closed__12;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_codeblock___closed__13;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_codeblock___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_codeblock() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_codeblock___closed__14;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_blockquote___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("blockquote", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_blockquote___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_blockquote___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_blockquote___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(">", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_blockquote___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_blockquote___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_blockquote___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_li___closed__4;
x_2 = l_Lean_Doc_Syntax_blockquote___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_blockquote___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_blockquote___closed__4;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_blockquote___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_blockquote() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_blockquote___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__ref___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("link_ref", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__ref___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_link__ref___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__ref___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]:", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__ref___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_link__ref___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__ref___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_link__ref___closed__3;
x_2 = l_Lean_Doc_Syntax_ref___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__ref___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = l_Lean_Doc_Syntax_link__ref___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__ref___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_link__ref___closed__5;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_link__ref___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_link__ref() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_link__ref___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote__ref___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("footnote_ref", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote__ref___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_footnote__ref___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote__ref___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[^", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote__ref___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_footnote__ref___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote__ref___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__str___closed__6;
x_2 = l_Lean_Doc_Syntax_footnote__ref___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote__ref___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_link__ref___closed__3;
x_2 = l_Lean_Doc_Syntax_footnote__ref___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote__ref___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_emph___closed__6;
x_2 = l_Lean_Doc_Syntax_footnote__ref___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote__ref___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_footnote__ref___closed__6;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_Doc_Syntax_footnote__ref___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_footnote__ref() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_footnote__ref___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("directive", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_directive___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":::", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_directive___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rawIdent", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_directive___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_directive___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_directive___closed__6;
x_2 = l_Lean_Doc_Syntax_directive___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__5;
x_2 = l_Lean_Doc_Syntax_directive___closed__7;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ol___closed__7;
x_2 = l_Lean_Doc_Syntax_directive___closed__8;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1024u);
x_2 = l_Lean_Doc_Syntax_block_quot___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_directive___closed__10;
x_2 = l_Lean_Doc_Syntax_emph___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_directive___closed__11;
x_2 = l_Lean_Doc_Syntax_directive___closed__9;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__8;
x_2 = l_Lean_Doc_Syntax_directive___closed__12;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_directive___closed__13;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_directive___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_directive() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_directive___closed__14;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("header", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_header___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("header(", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_header___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__num___closed__4;
x_2 = l_Lean_Doc_Syntax_header___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_arg__val_quot___closed__14;
x_2 = l_Lean_Doc_Syntax_header___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_ol___closed__7;
x_2 = l_Lean_Doc_Syntax_header___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_para___closed__6;
x_2 = l_Lean_Doc_Syntax_header___closed__6;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__8;
x_2 = l_Lean_Doc_Syntax_header___closed__7;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_header___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_header___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_header() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_header___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Term_structInstField;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__1;
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sepBy", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_li___closed__2;
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__5;
x_2 = l_Lean_Doc_Syntax_metadataContents___closed__0;
x_3 = l_Lean_Doc_Syntax_metadataContents___closed__4;
x_4 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("irrelevant", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__7;
x_2 = l_Lean_Parser_checkColGe(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__6;
x_2 = l_Lean_Doc_Syntax_metadataContents___closed__8;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__7;
x_2 = l_Lean_Parser_checkColEq(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("line break", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__11;
x_2 = l_Lean_Parser_checkLinebreakBefore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_pushNone;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__13;
x_2 = l_Lean_Doc_Syntax_metadataContents___closed__12;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__14;
x_2 = l_Lean_Doc_Syntax_metadataContents___closed__10;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__15;
x_2 = l_Lean_Doc_Syntax_metadataContents___closed__2;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__17() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Doc_Syntax_metadataContents___closed__16;
x_3 = l_Lean_Doc_Syntax_metadataContents___closed__1;
x_4 = l_Lean_Doc_Syntax_metadataContents___closed__9;
x_5 = l_Lean_Parser_sepBy(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__17;
x_2 = l_Lean_Parser_withPosition(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__18;
x_2 = l_Lean_Parser_Term_structInstFields(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__19;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("metadata_block", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_metadata__block___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("%%%", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadata__block___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("metadataContents", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_metadata__block___closed__4;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadata__block___closed__5;
x_2 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_metadata__block___closed__6;
x_2 = l_Lean_Doc_Syntax_metadata__block___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_metadata__block___closed__3;
x_2 = l_Lean_Doc_Syntax_metadata__block___closed__7;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_metadata__block___closed__8;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_metadata__block___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadata__block() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_metadata__block___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents_formatter___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_formatter), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_metadataContents_formatter___closed__1;
x_2 = l_Lean_Doc_Syntax_metadataContents___closed__1;
x_3 = l_Lean_Doc_Syntax_metadataContents_formatter___closed__0;
x_4 = lean_alloc_closure((void*)(l_Lean_Parser_sepByIndent_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Doc_Syntax_metadataContents_formatter___closed__2;
x_7 = l_Lean_Parser_Term_structInstFields_formatter(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Parser_Term_structInstField_parenthesizer), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_metadataContents___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_symbol_parenthesizer), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 1;
x_2 = l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1;
x_3 = l_Lean_Doc_Syntax_metadataContents___closed__1;
x_4 = l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0;
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_sepByIndent_parenthesizer___boxed), 9, 4);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2;
x_7 = l_Lean_Parser_Term_structInstFields_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_command___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_command___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Doc_Syntax_command___closed__0;
x_2 = l_Lean_Doc_Syntax_arg__str___closed__1;
x_3 = l_Lean_Doc_Syntax_arg__str___closed__0;
x_4 = l_Lean_Doc_Syntax_arg__val_quot___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_command___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("command{", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_command___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Doc_Syntax_command___closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_command___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_directive___closed__6;
x_2 = l_Lean_Doc_Syntax_command___closed__3;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_command___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__5;
x_2 = l_Lean_Doc_Syntax_command___closed__4;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_command___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_role___closed__8;
x_2 = l_Lean_Doc_Syntax_command___closed__5;
x_3 = l_Lean_Doc_Syntax_arg__val_quot___closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_command___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Doc_Syntax_command___closed__6;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Doc_Syntax_command___closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_command() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Doc_Syntax_command___closed__7;
return x_1;
}
}
lean_object* initialize_Init_Prelude(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Notation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Extra(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Syntax_arg__val_quot___closed__0 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__0);
l_Lean_Doc_Syntax_arg__val_quot___closed__1 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__1);
l_Lean_Doc_Syntax_arg__val_quot___closed__2 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__2);
l_Lean_Doc_Syntax_arg__val_quot___closed__3 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__3);
l_Lean_Doc_Syntax_arg__val_quot___closed__4 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__4);
l_Lean_Doc_Syntax_arg__val_quot___closed__5 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__5);
l_Lean_Doc_Syntax_arg__val_quot___closed__6 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__6);
l_Lean_Doc_Syntax_arg__val_quot___closed__7 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__7);
l_Lean_Doc_Syntax_arg__val_quot___closed__8 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__8);
l_Lean_Doc_Syntax_arg__val_quot___closed__9 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__9);
l_Lean_Doc_Syntax_arg__val_quot___closed__10 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__10();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__10);
l_Lean_Doc_Syntax_arg__val_quot___closed__11 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__11();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__11);
l_Lean_Doc_Syntax_arg__val_quot___closed__12 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__12();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__12);
l_Lean_Doc_Syntax_arg__val_quot___closed__13 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__13();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__13);
l_Lean_Doc_Syntax_arg__val_quot___closed__14 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__14();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__14);
l_Lean_Doc_Syntax_arg__val_quot___closed__15 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__15();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__15);
l_Lean_Doc_Syntax_arg__val_quot___closed__16 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__16();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__16);
l_Lean_Doc_Syntax_arg__val_quot___closed__17 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__17();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__17);
l_Lean_Doc_Syntax_arg__val_quot___closed__18 = _init_l_Lean_Doc_Syntax_arg__val_quot___closed__18();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot___closed__18);
l_Lean_Doc_Syntax_arg__val_quot = _init_l_Lean_Doc_Syntax_arg__val_quot();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__val_quot);
l_Lean_Parser_Category_arg__val = _init_l_Lean_Parser_Category_arg__val();
lean_mark_persistent(l_Lean_Parser_Category_arg__val);
l_Lean_Doc_Syntax_arg__str___closed__0 = _init_l_Lean_Doc_Syntax_arg__str___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__str___closed__0);
l_Lean_Doc_Syntax_arg__str___closed__1 = _init_l_Lean_Doc_Syntax_arg__str___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__str___closed__1);
l_Lean_Doc_Syntax_arg__str___closed__2 = _init_l_Lean_Doc_Syntax_arg__str___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__str___closed__2);
l_Lean_Doc_Syntax_arg__str___closed__3 = _init_l_Lean_Doc_Syntax_arg__str___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__str___closed__3);
l_Lean_Doc_Syntax_arg__str___closed__4 = _init_l_Lean_Doc_Syntax_arg__str___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__str___closed__4);
l_Lean_Doc_Syntax_arg__str___closed__5 = _init_l_Lean_Doc_Syntax_arg__str___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__str___closed__5);
l_Lean_Doc_Syntax_arg__str___closed__6 = _init_l_Lean_Doc_Syntax_arg__str___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__str___closed__6);
l_Lean_Doc_Syntax_arg__str___closed__7 = _init_l_Lean_Doc_Syntax_arg__str___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__str___closed__7);
l_Lean_Doc_Syntax_arg__str = _init_l_Lean_Doc_Syntax_arg__str();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__str);
l_Lean_Doc_Syntax_arg__ident___closed__0 = _init_l_Lean_Doc_Syntax_arg__ident___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__ident___closed__0);
l_Lean_Doc_Syntax_arg__ident___closed__1 = _init_l_Lean_Doc_Syntax_arg__ident___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__ident___closed__1);
l_Lean_Doc_Syntax_arg__ident___closed__2 = _init_l_Lean_Doc_Syntax_arg__ident___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__ident___closed__2);
l_Lean_Doc_Syntax_arg__ident___closed__3 = _init_l_Lean_Doc_Syntax_arg__ident___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__ident___closed__3);
l_Lean_Doc_Syntax_arg__ident___closed__4 = _init_l_Lean_Doc_Syntax_arg__ident___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__ident___closed__4);
l_Lean_Doc_Syntax_arg__ident___closed__5 = _init_l_Lean_Doc_Syntax_arg__ident___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__ident___closed__5);
l_Lean_Doc_Syntax_arg__ident = _init_l_Lean_Doc_Syntax_arg__ident();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__ident);
l_Lean_Doc_Syntax_arg__num___closed__0 = _init_l_Lean_Doc_Syntax_arg__num___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__num___closed__0);
l_Lean_Doc_Syntax_arg__num___closed__1 = _init_l_Lean_Doc_Syntax_arg__num___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__num___closed__1);
l_Lean_Doc_Syntax_arg__num___closed__2 = _init_l_Lean_Doc_Syntax_arg__num___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__num___closed__2);
l_Lean_Doc_Syntax_arg__num___closed__3 = _init_l_Lean_Doc_Syntax_arg__num___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__num___closed__3);
l_Lean_Doc_Syntax_arg__num___closed__4 = _init_l_Lean_Doc_Syntax_arg__num___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__num___closed__4);
l_Lean_Doc_Syntax_arg__num___closed__5 = _init_l_Lean_Doc_Syntax_arg__num___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__num___closed__5);
l_Lean_Doc_Syntax_arg__num = _init_l_Lean_Doc_Syntax_arg__num();
lean_mark_persistent(l_Lean_Doc_Syntax_arg__num);
l_Lean_Doc_Syntax_doc__arg_quot___closed__0 = _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot___closed__0);
l_Lean_Doc_Syntax_doc__arg_quot___closed__1 = _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot___closed__1);
l_Lean_Doc_Syntax_doc__arg_quot___closed__2 = _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot___closed__2);
l_Lean_Doc_Syntax_doc__arg_quot___closed__3 = _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot___closed__3);
l_Lean_Doc_Syntax_doc__arg_quot___closed__4 = _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot___closed__4);
l_Lean_Doc_Syntax_doc__arg_quot___closed__5 = _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot___closed__5);
l_Lean_Doc_Syntax_doc__arg_quot___closed__6 = _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot___closed__6);
l_Lean_Doc_Syntax_doc__arg_quot___closed__7 = _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot___closed__7);
l_Lean_Doc_Syntax_doc__arg_quot___closed__8 = _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot___closed__8);
l_Lean_Doc_Syntax_doc__arg_quot___closed__9 = _init_l_Lean_Doc_Syntax_doc__arg_quot___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot___closed__9);
l_Lean_Doc_Syntax_doc__arg_quot = _init_l_Lean_Doc_Syntax_doc__arg_quot();
lean_mark_persistent(l_Lean_Doc_Syntax_doc__arg_quot);
l_Lean_Parser_Category_doc__arg = _init_l_Lean_Parser_Category_doc__arg();
lean_mark_persistent(l_Lean_Parser_Category_doc__arg);
l_Lean_Doc_Syntax_anon___closed__0 = _init_l_Lean_Doc_Syntax_anon___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_anon___closed__0);
l_Lean_Doc_Syntax_anon___closed__1 = _init_l_Lean_Doc_Syntax_anon___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_anon___closed__1);
l_Lean_Doc_Syntax_anon___closed__2 = _init_l_Lean_Doc_Syntax_anon___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_anon___closed__2);
l_Lean_Doc_Syntax_anon = _init_l_Lean_Doc_Syntax_anon();
lean_mark_persistent(l_Lean_Doc_Syntax_anon);
l_Lean_Doc_Syntax_named___closed__0 = _init_l_Lean_Doc_Syntax_named___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__0);
l_Lean_Doc_Syntax_named___closed__1 = _init_l_Lean_Doc_Syntax_named___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__1);
l_Lean_Doc_Syntax_named___closed__2 = _init_l_Lean_Doc_Syntax_named___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__2);
l_Lean_Doc_Syntax_named___closed__3 = _init_l_Lean_Doc_Syntax_named___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__3);
l_Lean_Doc_Syntax_named___closed__4 = _init_l_Lean_Doc_Syntax_named___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__4);
l_Lean_Doc_Syntax_named___closed__5 = _init_l_Lean_Doc_Syntax_named___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__5);
l_Lean_Doc_Syntax_named___closed__6 = _init_l_Lean_Doc_Syntax_named___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__6);
l_Lean_Doc_Syntax_named___closed__7 = _init_l_Lean_Doc_Syntax_named___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__7);
l_Lean_Doc_Syntax_named___closed__8 = _init_l_Lean_Doc_Syntax_named___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__8);
l_Lean_Doc_Syntax_named___closed__9 = _init_l_Lean_Doc_Syntax_named___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__9);
l_Lean_Doc_Syntax_named___closed__10 = _init_l_Lean_Doc_Syntax_named___closed__10();
lean_mark_persistent(l_Lean_Doc_Syntax_named___closed__10);
l_Lean_Doc_Syntax_named = _init_l_Lean_Doc_Syntax_named();
lean_mark_persistent(l_Lean_Doc_Syntax_named);
l_Lean_Doc_Syntax_named__no__paren___closed__0 = _init_l_Lean_Doc_Syntax_named__no__paren___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_named__no__paren___closed__0);
l_Lean_Doc_Syntax_named__no__paren___closed__1 = _init_l_Lean_Doc_Syntax_named__no__paren___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_named__no__paren___closed__1);
l_Lean_Doc_Syntax_named__no__paren___closed__2 = _init_l_Lean_Doc_Syntax_named__no__paren___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_named__no__paren___closed__2);
l_Lean_Doc_Syntax_named__no__paren___closed__3 = _init_l_Lean_Doc_Syntax_named__no__paren___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_named__no__paren___closed__3);
l_Lean_Doc_Syntax_named__no__paren___closed__4 = _init_l_Lean_Doc_Syntax_named__no__paren___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_named__no__paren___closed__4);
l_Lean_Doc_Syntax_named__no__paren = _init_l_Lean_Doc_Syntax_named__no__paren();
lean_mark_persistent(l_Lean_Doc_Syntax_named__no__paren);
l_Lean_Doc_Syntax_flag__on___closed__0 = _init_l_Lean_Doc_Syntax_flag__on___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__on___closed__0);
l_Lean_Doc_Syntax_flag__on___closed__1 = _init_l_Lean_Doc_Syntax_flag__on___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__on___closed__1);
l_Lean_Doc_Syntax_flag__on___closed__2 = _init_l_Lean_Doc_Syntax_flag__on___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__on___closed__2);
l_Lean_Doc_Syntax_flag__on___closed__3 = _init_l_Lean_Doc_Syntax_flag__on___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__on___closed__3);
l_Lean_Doc_Syntax_flag__on___closed__4 = _init_l_Lean_Doc_Syntax_flag__on___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__on___closed__4);
l_Lean_Doc_Syntax_flag__on___closed__5 = _init_l_Lean_Doc_Syntax_flag__on___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__on___closed__5);
l_Lean_Doc_Syntax_flag__on = _init_l_Lean_Doc_Syntax_flag__on();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__on);
l_Lean_Doc_Syntax_flag__off___closed__0 = _init_l_Lean_Doc_Syntax_flag__off___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__off___closed__0);
l_Lean_Doc_Syntax_flag__off___closed__1 = _init_l_Lean_Doc_Syntax_flag__off___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__off___closed__1);
l_Lean_Doc_Syntax_flag__off___closed__2 = _init_l_Lean_Doc_Syntax_flag__off___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__off___closed__2);
l_Lean_Doc_Syntax_flag__off___closed__3 = _init_l_Lean_Doc_Syntax_flag__off___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__off___closed__3);
l_Lean_Doc_Syntax_flag__off___closed__4 = _init_l_Lean_Doc_Syntax_flag__off___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__off___closed__4);
l_Lean_Doc_Syntax_flag__off___closed__5 = _init_l_Lean_Doc_Syntax_flag__off___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__off___closed__5);
l_Lean_Doc_Syntax_flag__off = _init_l_Lean_Doc_Syntax_flag__off();
lean_mark_persistent(l_Lean_Doc_Syntax_flag__off);
l_Lean_Doc_Syntax_link__target_quot___closed__0 = _init_l_Lean_Doc_Syntax_link__target_quot___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot___closed__0);
l_Lean_Doc_Syntax_link__target_quot___closed__1 = _init_l_Lean_Doc_Syntax_link__target_quot___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot___closed__1);
l_Lean_Doc_Syntax_link__target_quot___closed__2 = _init_l_Lean_Doc_Syntax_link__target_quot___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot___closed__2);
l_Lean_Doc_Syntax_link__target_quot___closed__3 = _init_l_Lean_Doc_Syntax_link__target_quot___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot___closed__3);
l_Lean_Doc_Syntax_link__target_quot___closed__4 = _init_l_Lean_Doc_Syntax_link__target_quot___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot___closed__4);
l_Lean_Doc_Syntax_link__target_quot___closed__5 = _init_l_Lean_Doc_Syntax_link__target_quot___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot___closed__5);
l_Lean_Doc_Syntax_link__target_quot___closed__6 = _init_l_Lean_Doc_Syntax_link__target_quot___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot___closed__6);
l_Lean_Doc_Syntax_link__target_quot___closed__7 = _init_l_Lean_Doc_Syntax_link__target_quot___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot___closed__7);
l_Lean_Doc_Syntax_link__target_quot___closed__8 = _init_l_Lean_Doc_Syntax_link__target_quot___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot___closed__8);
l_Lean_Doc_Syntax_link__target_quot___closed__9 = _init_l_Lean_Doc_Syntax_link__target_quot___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot___closed__9);
l_Lean_Doc_Syntax_link__target_quot = _init_l_Lean_Doc_Syntax_link__target_quot();
lean_mark_persistent(l_Lean_Doc_Syntax_link__target_quot);
l_Lean_Parser_Category_link__target = _init_l_Lean_Parser_Category_link__target();
lean_mark_persistent(l_Lean_Parser_Category_link__target);
l_Lean_Doc_Syntax_url___closed__0 = _init_l_Lean_Doc_Syntax_url___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_url___closed__0);
l_Lean_Doc_Syntax_url___closed__1 = _init_l_Lean_Doc_Syntax_url___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_url___closed__1);
l_Lean_Doc_Syntax_url___closed__2 = _init_l_Lean_Doc_Syntax_url___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_url___closed__2);
l_Lean_Doc_Syntax_url___closed__3 = _init_l_Lean_Doc_Syntax_url___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_url___closed__3);
l_Lean_Doc_Syntax_url___closed__4 = _init_l_Lean_Doc_Syntax_url___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_url___closed__4);
l_Lean_Doc_Syntax_url = _init_l_Lean_Doc_Syntax_url();
lean_mark_persistent(l_Lean_Doc_Syntax_url);
l_Lean_Doc_Syntax_ref___closed__0 = _init_l_Lean_Doc_Syntax_ref___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_ref___closed__0);
l_Lean_Doc_Syntax_ref___closed__1 = _init_l_Lean_Doc_Syntax_ref___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_ref___closed__1);
l_Lean_Doc_Syntax_ref___closed__2 = _init_l_Lean_Doc_Syntax_ref___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_ref___closed__2);
l_Lean_Doc_Syntax_ref___closed__3 = _init_l_Lean_Doc_Syntax_ref___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_ref___closed__3);
l_Lean_Doc_Syntax_ref___closed__4 = _init_l_Lean_Doc_Syntax_ref___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_ref___closed__4);
l_Lean_Doc_Syntax_ref___closed__5 = _init_l_Lean_Doc_Syntax_ref___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_ref___closed__5);
l_Lean_Doc_Syntax_ref___closed__6 = _init_l_Lean_Doc_Syntax_ref___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_ref___closed__6);
l_Lean_Doc_Syntax_ref___closed__7 = _init_l_Lean_Doc_Syntax_ref___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_ref___closed__7);
l_Lean_Doc_Syntax_ref___closed__8 = _init_l_Lean_Doc_Syntax_ref___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_ref___closed__8);
l_Lean_Doc_Syntax_ref = _init_l_Lean_Doc_Syntax_ref();
lean_mark_persistent(l_Lean_Doc_Syntax_ref);
l_Lean_Doc_Syntax_inline_quot___closed__0 = _init_l_Lean_Doc_Syntax_inline_quot___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot___closed__0);
l_Lean_Doc_Syntax_inline_quot___closed__1 = _init_l_Lean_Doc_Syntax_inline_quot___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot___closed__1);
l_Lean_Doc_Syntax_inline_quot___closed__2 = _init_l_Lean_Doc_Syntax_inline_quot___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot___closed__2);
l_Lean_Doc_Syntax_inline_quot___closed__3 = _init_l_Lean_Doc_Syntax_inline_quot___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot___closed__3);
l_Lean_Doc_Syntax_inline_quot___closed__4 = _init_l_Lean_Doc_Syntax_inline_quot___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot___closed__4);
l_Lean_Doc_Syntax_inline_quot___closed__5 = _init_l_Lean_Doc_Syntax_inline_quot___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot___closed__5);
l_Lean_Doc_Syntax_inline_quot___closed__6 = _init_l_Lean_Doc_Syntax_inline_quot___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot___closed__6);
l_Lean_Doc_Syntax_inline_quot___closed__7 = _init_l_Lean_Doc_Syntax_inline_quot___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot___closed__7);
l_Lean_Doc_Syntax_inline_quot___closed__8 = _init_l_Lean_Doc_Syntax_inline_quot___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot___closed__8);
l_Lean_Doc_Syntax_inline_quot___closed__9 = _init_l_Lean_Doc_Syntax_inline_quot___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot___closed__9);
l_Lean_Doc_Syntax_inline_quot = _init_l_Lean_Doc_Syntax_inline_quot();
lean_mark_persistent(l_Lean_Doc_Syntax_inline_quot);
l_Lean_Parser_Category_inline = _init_l_Lean_Parser_Category_inline();
lean_mark_persistent(l_Lean_Parser_Category_inline);
l_Lean_Doc_Syntax_text___closed__0 = _init_l_Lean_Doc_Syntax_text___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_text___closed__0);
l_Lean_Doc_Syntax_text___closed__1 = _init_l_Lean_Doc_Syntax_text___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_text___closed__1);
l_Lean_Doc_Syntax_text___closed__2 = _init_l_Lean_Doc_Syntax_text___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_text___closed__2);
l_Lean_Doc_Syntax_text = _init_l_Lean_Doc_Syntax_text();
lean_mark_persistent(l_Lean_Doc_Syntax_text);
l_Lean_Doc_Syntax_emph___closed__0 = _init_l_Lean_Doc_Syntax_emph___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_emph___closed__0);
l_Lean_Doc_Syntax_emph___closed__1 = _init_l_Lean_Doc_Syntax_emph___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_emph___closed__1);
l_Lean_Doc_Syntax_emph___closed__2 = _init_l_Lean_Doc_Syntax_emph___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_emph___closed__2);
l_Lean_Doc_Syntax_emph___closed__3 = _init_l_Lean_Doc_Syntax_emph___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_emph___closed__3);
l_Lean_Doc_Syntax_emph___closed__4 = _init_l_Lean_Doc_Syntax_emph___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_emph___closed__4);
l_Lean_Doc_Syntax_emph___closed__5 = _init_l_Lean_Doc_Syntax_emph___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_emph___closed__5);
l_Lean_Doc_Syntax_emph___closed__6 = _init_l_Lean_Doc_Syntax_emph___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_emph___closed__6);
l_Lean_Doc_Syntax_emph___closed__7 = _init_l_Lean_Doc_Syntax_emph___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_emph___closed__7);
l_Lean_Doc_Syntax_emph___closed__8 = _init_l_Lean_Doc_Syntax_emph___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_emph___closed__8);
l_Lean_Doc_Syntax_emph___closed__9 = _init_l_Lean_Doc_Syntax_emph___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_emph___closed__9);
l_Lean_Doc_Syntax_emph = _init_l_Lean_Doc_Syntax_emph();
lean_mark_persistent(l_Lean_Doc_Syntax_emph);
l_Lean_Doc_Syntax_bold___closed__0 = _init_l_Lean_Doc_Syntax_bold___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_bold___closed__0);
l_Lean_Doc_Syntax_bold___closed__1 = _init_l_Lean_Doc_Syntax_bold___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_bold___closed__1);
l_Lean_Doc_Syntax_bold___closed__2 = _init_l_Lean_Doc_Syntax_bold___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_bold___closed__2);
l_Lean_Doc_Syntax_bold___closed__3 = _init_l_Lean_Doc_Syntax_bold___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_bold___closed__3);
l_Lean_Doc_Syntax_bold___closed__4 = _init_l_Lean_Doc_Syntax_bold___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_bold___closed__4);
l_Lean_Doc_Syntax_bold___closed__5 = _init_l_Lean_Doc_Syntax_bold___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_bold___closed__5);
l_Lean_Doc_Syntax_bold___closed__6 = _init_l_Lean_Doc_Syntax_bold___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_bold___closed__6);
l_Lean_Doc_Syntax_bold = _init_l_Lean_Doc_Syntax_bold();
lean_mark_persistent(l_Lean_Doc_Syntax_bold);
l_Lean_Doc_Syntax_link___closed__0 = _init_l_Lean_Doc_Syntax_link___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_link___closed__0);
l_Lean_Doc_Syntax_link___closed__1 = _init_l_Lean_Doc_Syntax_link___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_link___closed__1);
l_Lean_Doc_Syntax_link___closed__2 = _init_l_Lean_Doc_Syntax_link___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_link___closed__2);
l_Lean_Doc_Syntax_link___closed__3 = _init_l_Lean_Doc_Syntax_link___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_link___closed__3);
l_Lean_Doc_Syntax_link___closed__4 = _init_l_Lean_Doc_Syntax_link___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_link___closed__4);
l_Lean_Doc_Syntax_link___closed__5 = _init_l_Lean_Doc_Syntax_link___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_link___closed__5);
l_Lean_Doc_Syntax_link___closed__6 = _init_l_Lean_Doc_Syntax_link___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_link___closed__6);
l_Lean_Doc_Syntax_link___closed__7 = _init_l_Lean_Doc_Syntax_link___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_link___closed__7);
l_Lean_Doc_Syntax_link = _init_l_Lean_Doc_Syntax_link();
lean_mark_persistent(l_Lean_Doc_Syntax_link);
l_Lean_Doc_Syntax_image___closed__0 = _init_l_Lean_Doc_Syntax_image___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_image___closed__0);
l_Lean_Doc_Syntax_image___closed__1 = _init_l_Lean_Doc_Syntax_image___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_image___closed__1);
l_Lean_Doc_Syntax_image___closed__2 = _init_l_Lean_Doc_Syntax_image___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_image___closed__2);
l_Lean_Doc_Syntax_image___closed__3 = _init_l_Lean_Doc_Syntax_image___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_image___closed__3);
l_Lean_Doc_Syntax_image___closed__4 = _init_l_Lean_Doc_Syntax_image___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_image___closed__4);
l_Lean_Doc_Syntax_image___closed__5 = _init_l_Lean_Doc_Syntax_image___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_image___closed__5);
l_Lean_Doc_Syntax_image___closed__6 = _init_l_Lean_Doc_Syntax_image___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_image___closed__6);
l_Lean_Doc_Syntax_image___closed__7 = _init_l_Lean_Doc_Syntax_image___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_image___closed__7);
l_Lean_Doc_Syntax_image = _init_l_Lean_Doc_Syntax_image();
lean_mark_persistent(l_Lean_Doc_Syntax_image);
l_Lean_Doc_Syntax_footnote___closed__0 = _init_l_Lean_Doc_Syntax_footnote___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote___closed__0);
l_Lean_Doc_Syntax_footnote___closed__1 = _init_l_Lean_Doc_Syntax_footnote___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote___closed__1);
l_Lean_Doc_Syntax_footnote___closed__2 = _init_l_Lean_Doc_Syntax_footnote___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote___closed__2);
l_Lean_Doc_Syntax_footnote___closed__3 = _init_l_Lean_Doc_Syntax_footnote___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote___closed__3);
l_Lean_Doc_Syntax_footnote___closed__4 = _init_l_Lean_Doc_Syntax_footnote___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote___closed__4);
l_Lean_Doc_Syntax_footnote___closed__5 = _init_l_Lean_Doc_Syntax_footnote___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote___closed__5);
l_Lean_Doc_Syntax_footnote___closed__6 = _init_l_Lean_Doc_Syntax_footnote___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote___closed__6);
l_Lean_Doc_Syntax_footnote = _init_l_Lean_Doc_Syntax_footnote();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote);
l_Lean_Doc_Syntax_linebreak___closed__0 = _init_l_Lean_Doc_Syntax_linebreak___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_linebreak___closed__0);
l_Lean_Doc_Syntax_linebreak___closed__1 = _init_l_Lean_Doc_Syntax_linebreak___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_linebreak___closed__1);
l_Lean_Doc_Syntax_linebreak___closed__2 = _init_l_Lean_Doc_Syntax_linebreak___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_linebreak___closed__2);
l_Lean_Doc_Syntax_linebreak___closed__3 = _init_l_Lean_Doc_Syntax_linebreak___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_linebreak___closed__3);
l_Lean_Doc_Syntax_linebreak___closed__4 = _init_l_Lean_Doc_Syntax_linebreak___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_linebreak___closed__4);
l_Lean_Doc_Syntax_linebreak___closed__5 = _init_l_Lean_Doc_Syntax_linebreak___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_linebreak___closed__5);
l_Lean_Doc_Syntax_linebreak = _init_l_Lean_Doc_Syntax_linebreak();
lean_mark_persistent(l_Lean_Doc_Syntax_linebreak);
l_Lean_Doc_Syntax_code___closed__0 = _init_l_Lean_Doc_Syntax_code___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_code___closed__0);
l_Lean_Doc_Syntax_code___closed__1 = _init_l_Lean_Doc_Syntax_code___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_code___closed__1);
l_Lean_Doc_Syntax_code___closed__2 = _init_l_Lean_Doc_Syntax_code___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_code___closed__2);
l_Lean_Doc_Syntax_code___closed__3 = _init_l_Lean_Doc_Syntax_code___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_code___closed__3);
l_Lean_Doc_Syntax_code___closed__4 = _init_l_Lean_Doc_Syntax_code___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_code___closed__4);
l_Lean_Doc_Syntax_code___closed__5 = _init_l_Lean_Doc_Syntax_code___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_code___closed__5);
l_Lean_Doc_Syntax_code___closed__6 = _init_l_Lean_Doc_Syntax_code___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_code___closed__6);
l_Lean_Doc_Syntax_code = _init_l_Lean_Doc_Syntax_code();
lean_mark_persistent(l_Lean_Doc_Syntax_code);
l_Lean_Doc_Syntax_role___closed__0 = _init_l_Lean_Doc_Syntax_role___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__0);
l_Lean_Doc_Syntax_role___closed__1 = _init_l_Lean_Doc_Syntax_role___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__1);
l_Lean_Doc_Syntax_role___closed__2 = _init_l_Lean_Doc_Syntax_role___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__2);
l_Lean_Doc_Syntax_role___closed__3 = _init_l_Lean_Doc_Syntax_role___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__3);
l_Lean_Doc_Syntax_role___closed__4 = _init_l_Lean_Doc_Syntax_role___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__4);
l_Lean_Doc_Syntax_role___closed__5 = _init_l_Lean_Doc_Syntax_role___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__5);
l_Lean_Doc_Syntax_role___closed__6 = _init_l_Lean_Doc_Syntax_role___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__6);
l_Lean_Doc_Syntax_role___closed__7 = _init_l_Lean_Doc_Syntax_role___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__7);
l_Lean_Doc_Syntax_role___closed__8 = _init_l_Lean_Doc_Syntax_role___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__8);
l_Lean_Doc_Syntax_role___closed__9 = _init_l_Lean_Doc_Syntax_role___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__9);
l_Lean_Doc_Syntax_role___closed__10 = _init_l_Lean_Doc_Syntax_role___closed__10();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__10);
l_Lean_Doc_Syntax_role___closed__11 = _init_l_Lean_Doc_Syntax_role___closed__11();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__11);
l_Lean_Doc_Syntax_role___closed__12 = _init_l_Lean_Doc_Syntax_role___closed__12();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__12);
l_Lean_Doc_Syntax_role___closed__13 = _init_l_Lean_Doc_Syntax_role___closed__13();
lean_mark_persistent(l_Lean_Doc_Syntax_role___closed__13);
l_Lean_Doc_Syntax_role = _init_l_Lean_Doc_Syntax_role();
lean_mark_persistent(l_Lean_Doc_Syntax_role);
l_Lean_Doc_Syntax_inline__math___closed__0 = _init_l_Lean_Doc_Syntax_inline__math___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_inline__math___closed__0);
l_Lean_Doc_Syntax_inline__math___closed__1 = _init_l_Lean_Doc_Syntax_inline__math___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_inline__math___closed__1);
l_Lean_Doc_Syntax_inline__math___closed__2 = _init_l_Lean_Doc_Syntax_inline__math___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_inline__math___closed__2);
l_Lean_Doc_Syntax_inline__math___closed__3 = _init_l_Lean_Doc_Syntax_inline__math___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_inline__math___closed__3);
l_Lean_Doc_Syntax_inline__math___closed__4 = _init_l_Lean_Doc_Syntax_inline__math___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_inline__math___closed__4);
l_Lean_Doc_Syntax_inline__math___closed__5 = _init_l_Lean_Doc_Syntax_inline__math___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_inline__math___closed__5);
l_Lean_Doc_Syntax_inline__math = _init_l_Lean_Doc_Syntax_inline__math();
lean_mark_persistent(l_Lean_Doc_Syntax_inline__math);
l_Lean_Doc_Syntax_display__math___closed__0 = _init_l_Lean_Doc_Syntax_display__math___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_display__math___closed__0);
l_Lean_Doc_Syntax_display__math___closed__1 = _init_l_Lean_Doc_Syntax_display__math___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_display__math___closed__1);
l_Lean_Doc_Syntax_display__math___closed__2 = _init_l_Lean_Doc_Syntax_display__math___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_display__math___closed__2);
l_Lean_Doc_Syntax_display__math___closed__3 = _init_l_Lean_Doc_Syntax_display__math___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_display__math___closed__3);
l_Lean_Doc_Syntax_display__math___closed__4 = _init_l_Lean_Doc_Syntax_display__math___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_display__math___closed__4);
l_Lean_Doc_Syntax_display__math___closed__5 = _init_l_Lean_Doc_Syntax_display__math___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_display__math___closed__5);
l_Lean_Doc_Syntax_display__math = _init_l_Lean_Doc_Syntax_display__math();
lean_mark_persistent(l_Lean_Doc_Syntax_display__math);
l_Lean_Doc_Syntax_block_quot___closed__0 = _init_l_Lean_Doc_Syntax_block_quot___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot___closed__0);
l_Lean_Doc_Syntax_block_quot___closed__1 = _init_l_Lean_Doc_Syntax_block_quot___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot___closed__1);
l_Lean_Doc_Syntax_block_quot___closed__2 = _init_l_Lean_Doc_Syntax_block_quot___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot___closed__2);
l_Lean_Doc_Syntax_block_quot___closed__3 = _init_l_Lean_Doc_Syntax_block_quot___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot___closed__3);
l_Lean_Doc_Syntax_block_quot___closed__4 = _init_l_Lean_Doc_Syntax_block_quot___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot___closed__4);
l_Lean_Doc_Syntax_block_quot___closed__5 = _init_l_Lean_Doc_Syntax_block_quot___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot___closed__5);
l_Lean_Doc_Syntax_block_quot___closed__6 = _init_l_Lean_Doc_Syntax_block_quot___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot___closed__6);
l_Lean_Doc_Syntax_block_quot___closed__7 = _init_l_Lean_Doc_Syntax_block_quot___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot___closed__7);
l_Lean_Doc_Syntax_block_quot___closed__8 = _init_l_Lean_Doc_Syntax_block_quot___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot___closed__8);
l_Lean_Doc_Syntax_block_quot___closed__9 = _init_l_Lean_Doc_Syntax_block_quot___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot___closed__9);
l_Lean_Doc_Syntax_block_quot = _init_l_Lean_Doc_Syntax_block_quot();
lean_mark_persistent(l_Lean_Doc_Syntax_block_quot);
l_Lean_Parser_Category_block = _init_l_Lean_Parser_Category_block();
lean_mark_persistent(l_Lean_Parser_Category_block);
l_Lean_Doc_Syntax_list__item_quot___closed__0 = _init_l_Lean_Doc_Syntax_list__item_quot___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot___closed__0);
l_Lean_Doc_Syntax_list__item_quot___closed__1 = _init_l_Lean_Doc_Syntax_list__item_quot___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot___closed__1);
l_Lean_Doc_Syntax_list__item_quot___closed__2 = _init_l_Lean_Doc_Syntax_list__item_quot___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot___closed__2);
l_Lean_Doc_Syntax_list__item_quot___closed__3 = _init_l_Lean_Doc_Syntax_list__item_quot___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot___closed__3);
l_Lean_Doc_Syntax_list__item_quot___closed__4 = _init_l_Lean_Doc_Syntax_list__item_quot___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot___closed__4);
l_Lean_Doc_Syntax_list__item_quot___closed__5 = _init_l_Lean_Doc_Syntax_list__item_quot___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot___closed__5);
l_Lean_Doc_Syntax_list__item_quot___closed__6 = _init_l_Lean_Doc_Syntax_list__item_quot___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot___closed__6);
l_Lean_Doc_Syntax_list__item_quot___closed__7 = _init_l_Lean_Doc_Syntax_list__item_quot___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot___closed__7);
l_Lean_Doc_Syntax_list__item_quot___closed__8 = _init_l_Lean_Doc_Syntax_list__item_quot___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot___closed__8);
l_Lean_Doc_Syntax_list__item_quot___closed__9 = _init_l_Lean_Doc_Syntax_list__item_quot___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot___closed__9);
l_Lean_Doc_Syntax_list__item_quot = _init_l_Lean_Doc_Syntax_list__item_quot();
lean_mark_persistent(l_Lean_Doc_Syntax_list__item_quot);
l_Lean_Parser_Category_list__item = _init_l_Lean_Parser_Category_list__item();
lean_mark_persistent(l_Lean_Parser_Category_list__item);
l_Lean_Doc_Syntax_li___closed__0 = _init_l_Lean_Doc_Syntax_li___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_li___closed__0);
l_Lean_Doc_Syntax_li___closed__1 = _init_l_Lean_Doc_Syntax_li___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_li___closed__1);
l_Lean_Doc_Syntax_li___closed__2 = _init_l_Lean_Doc_Syntax_li___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_li___closed__2);
l_Lean_Doc_Syntax_li___closed__3 = _init_l_Lean_Doc_Syntax_li___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_li___closed__3);
l_Lean_Doc_Syntax_li___closed__4 = _init_l_Lean_Doc_Syntax_li___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_li___closed__4);
l_Lean_Doc_Syntax_li___closed__5 = _init_l_Lean_Doc_Syntax_li___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_li___closed__5);
l_Lean_Doc_Syntax_li___closed__6 = _init_l_Lean_Doc_Syntax_li___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_li___closed__6);
l_Lean_Doc_Syntax_li = _init_l_Lean_Doc_Syntax_li();
lean_mark_persistent(l_Lean_Doc_Syntax_li);
l_Lean_Doc_Syntax_desc__item_quot___closed__0 = _init_l_Lean_Doc_Syntax_desc__item_quot___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot___closed__0);
l_Lean_Doc_Syntax_desc__item_quot___closed__1 = _init_l_Lean_Doc_Syntax_desc__item_quot___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot___closed__1);
l_Lean_Doc_Syntax_desc__item_quot___closed__2 = _init_l_Lean_Doc_Syntax_desc__item_quot___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot___closed__2);
l_Lean_Doc_Syntax_desc__item_quot___closed__3 = _init_l_Lean_Doc_Syntax_desc__item_quot___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot___closed__3);
l_Lean_Doc_Syntax_desc__item_quot___closed__4 = _init_l_Lean_Doc_Syntax_desc__item_quot___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot___closed__4);
l_Lean_Doc_Syntax_desc__item_quot___closed__5 = _init_l_Lean_Doc_Syntax_desc__item_quot___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot___closed__5);
l_Lean_Doc_Syntax_desc__item_quot___closed__6 = _init_l_Lean_Doc_Syntax_desc__item_quot___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot___closed__6);
l_Lean_Doc_Syntax_desc__item_quot___closed__7 = _init_l_Lean_Doc_Syntax_desc__item_quot___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot___closed__7);
l_Lean_Doc_Syntax_desc__item_quot___closed__8 = _init_l_Lean_Doc_Syntax_desc__item_quot___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot___closed__8);
l_Lean_Doc_Syntax_desc__item_quot___closed__9 = _init_l_Lean_Doc_Syntax_desc__item_quot___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot___closed__9);
l_Lean_Doc_Syntax_desc__item_quot = _init_l_Lean_Doc_Syntax_desc__item_quot();
lean_mark_persistent(l_Lean_Doc_Syntax_desc__item_quot);
l_Lean_Parser_Category_desc__item = _init_l_Lean_Parser_Category_desc__item();
lean_mark_persistent(l_Lean_Parser_Category_desc__item);
l_Lean_Doc_Syntax_desc___closed__0 = _init_l_Lean_Doc_Syntax_desc___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_desc___closed__0);
l_Lean_Doc_Syntax_desc___closed__1 = _init_l_Lean_Doc_Syntax_desc___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_desc___closed__1);
l_Lean_Doc_Syntax_desc___closed__2 = _init_l_Lean_Doc_Syntax_desc___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_desc___closed__2);
l_Lean_Doc_Syntax_desc___closed__3 = _init_l_Lean_Doc_Syntax_desc___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_desc___closed__3);
l_Lean_Doc_Syntax_desc___closed__4 = _init_l_Lean_Doc_Syntax_desc___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_desc___closed__4);
l_Lean_Doc_Syntax_desc___closed__5 = _init_l_Lean_Doc_Syntax_desc___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_desc___closed__5);
l_Lean_Doc_Syntax_desc___closed__6 = _init_l_Lean_Doc_Syntax_desc___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_desc___closed__6);
l_Lean_Doc_Syntax_desc___closed__7 = _init_l_Lean_Doc_Syntax_desc___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_desc___closed__7);
l_Lean_Doc_Syntax_desc___closed__8 = _init_l_Lean_Doc_Syntax_desc___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_desc___closed__8);
l_Lean_Doc_Syntax_desc___closed__9 = _init_l_Lean_Doc_Syntax_desc___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_desc___closed__9);
l_Lean_Doc_Syntax_desc = _init_l_Lean_Doc_Syntax_desc();
lean_mark_persistent(l_Lean_Doc_Syntax_desc);
l_Lean_Doc_Syntax_para___closed__0 = _init_l_Lean_Doc_Syntax_para___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_para___closed__0);
l_Lean_Doc_Syntax_para___closed__1 = _init_l_Lean_Doc_Syntax_para___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_para___closed__1);
l_Lean_Doc_Syntax_para___closed__2 = _init_l_Lean_Doc_Syntax_para___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_para___closed__2);
l_Lean_Doc_Syntax_para___closed__3 = _init_l_Lean_Doc_Syntax_para___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_para___closed__3);
l_Lean_Doc_Syntax_para___closed__4 = _init_l_Lean_Doc_Syntax_para___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_para___closed__4);
l_Lean_Doc_Syntax_para___closed__5 = _init_l_Lean_Doc_Syntax_para___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_para___closed__5);
l_Lean_Doc_Syntax_para___closed__6 = _init_l_Lean_Doc_Syntax_para___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_para___closed__6);
l_Lean_Doc_Syntax_para___closed__7 = _init_l_Lean_Doc_Syntax_para___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_para___closed__7);
l_Lean_Doc_Syntax_para___closed__8 = _init_l_Lean_Doc_Syntax_para___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_para___closed__8);
l_Lean_Doc_Syntax_para___closed__9 = _init_l_Lean_Doc_Syntax_para___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_para___closed__9);
l_Lean_Doc_Syntax_para = _init_l_Lean_Doc_Syntax_para();
lean_mark_persistent(l_Lean_Doc_Syntax_para);
l_Lean_Doc_Syntax_ul___closed__0 = _init_l_Lean_Doc_Syntax_ul___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_ul___closed__0);
l_Lean_Doc_Syntax_ul___closed__1 = _init_l_Lean_Doc_Syntax_ul___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_ul___closed__1);
l_Lean_Doc_Syntax_ul___closed__2 = _init_l_Lean_Doc_Syntax_ul___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_ul___closed__2);
l_Lean_Doc_Syntax_ul___closed__3 = _init_l_Lean_Doc_Syntax_ul___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_ul___closed__3);
l_Lean_Doc_Syntax_ul___closed__4 = _init_l_Lean_Doc_Syntax_ul___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_ul___closed__4);
l_Lean_Doc_Syntax_ul___closed__5 = _init_l_Lean_Doc_Syntax_ul___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_ul___closed__5);
l_Lean_Doc_Syntax_ul___closed__6 = _init_l_Lean_Doc_Syntax_ul___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_ul___closed__6);
l_Lean_Doc_Syntax_ul___closed__7 = _init_l_Lean_Doc_Syntax_ul___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_ul___closed__7);
l_Lean_Doc_Syntax_ul = _init_l_Lean_Doc_Syntax_ul();
lean_mark_persistent(l_Lean_Doc_Syntax_ul);
l_Lean_Doc_Syntax_dl___closed__0 = _init_l_Lean_Doc_Syntax_dl___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_dl___closed__0);
l_Lean_Doc_Syntax_dl___closed__1 = _init_l_Lean_Doc_Syntax_dl___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_dl___closed__1);
l_Lean_Doc_Syntax_dl___closed__2 = _init_l_Lean_Doc_Syntax_dl___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_dl___closed__2);
l_Lean_Doc_Syntax_dl___closed__3 = _init_l_Lean_Doc_Syntax_dl___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_dl___closed__3);
l_Lean_Doc_Syntax_dl___closed__4 = _init_l_Lean_Doc_Syntax_dl___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_dl___closed__4);
l_Lean_Doc_Syntax_dl___closed__5 = _init_l_Lean_Doc_Syntax_dl___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_dl___closed__5);
l_Lean_Doc_Syntax_dl___closed__6 = _init_l_Lean_Doc_Syntax_dl___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_dl___closed__6);
l_Lean_Doc_Syntax_dl___closed__7 = _init_l_Lean_Doc_Syntax_dl___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_dl___closed__7);
l_Lean_Doc_Syntax_dl = _init_l_Lean_Doc_Syntax_dl();
lean_mark_persistent(l_Lean_Doc_Syntax_dl);
l_Lean_Doc_Syntax_ol___closed__0 = _init_l_Lean_Doc_Syntax_ol___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__0);
l_Lean_Doc_Syntax_ol___closed__1 = _init_l_Lean_Doc_Syntax_ol___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__1);
l_Lean_Doc_Syntax_ol___closed__2 = _init_l_Lean_Doc_Syntax_ol___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__2);
l_Lean_Doc_Syntax_ol___closed__3 = _init_l_Lean_Doc_Syntax_ol___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__3);
l_Lean_Doc_Syntax_ol___closed__4 = _init_l_Lean_Doc_Syntax_ol___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__4);
l_Lean_Doc_Syntax_ol___closed__5 = _init_l_Lean_Doc_Syntax_ol___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__5);
l_Lean_Doc_Syntax_ol___closed__6 = _init_l_Lean_Doc_Syntax_ol___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__6);
l_Lean_Doc_Syntax_ol___closed__7 = _init_l_Lean_Doc_Syntax_ol___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__7);
l_Lean_Doc_Syntax_ol___closed__8 = _init_l_Lean_Doc_Syntax_ol___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__8);
l_Lean_Doc_Syntax_ol___closed__9 = _init_l_Lean_Doc_Syntax_ol___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__9);
l_Lean_Doc_Syntax_ol___closed__10 = _init_l_Lean_Doc_Syntax_ol___closed__10();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__10);
l_Lean_Doc_Syntax_ol___closed__11 = _init_l_Lean_Doc_Syntax_ol___closed__11();
lean_mark_persistent(l_Lean_Doc_Syntax_ol___closed__11);
l_Lean_Doc_Syntax_ol = _init_l_Lean_Doc_Syntax_ol();
lean_mark_persistent(l_Lean_Doc_Syntax_ol);
l_Lean_Doc_Syntax_codeblock___closed__0 = _init_l_Lean_Doc_Syntax_codeblock___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__0);
l_Lean_Doc_Syntax_codeblock___closed__1 = _init_l_Lean_Doc_Syntax_codeblock___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__1);
l_Lean_Doc_Syntax_codeblock___closed__2 = _init_l_Lean_Doc_Syntax_codeblock___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__2);
l_Lean_Doc_Syntax_codeblock___closed__3 = _init_l_Lean_Doc_Syntax_codeblock___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__3);
l_Lean_Doc_Syntax_codeblock___closed__4 = _init_l_Lean_Doc_Syntax_codeblock___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__4);
l_Lean_Doc_Syntax_codeblock___closed__5 = _init_l_Lean_Doc_Syntax_codeblock___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__5);
l_Lean_Doc_Syntax_codeblock___closed__6 = _init_l_Lean_Doc_Syntax_codeblock___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__6);
l_Lean_Doc_Syntax_codeblock___closed__7 = _init_l_Lean_Doc_Syntax_codeblock___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__7);
l_Lean_Doc_Syntax_codeblock___closed__8 = _init_l_Lean_Doc_Syntax_codeblock___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__8);
l_Lean_Doc_Syntax_codeblock___closed__9 = _init_l_Lean_Doc_Syntax_codeblock___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__9);
l_Lean_Doc_Syntax_codeblock___closed__10 = _init_l_Lean_Doc_Syntax_codeblock___closed__10();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__10);
l_Lean_Doc_Syntax_codeblock___closed__11 = _init_l_Lean_Doc_Syntax_codeblock___closed__11();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__11);
l_Lean_Doc_Syntax_codeblock___closed__12 = _init_l_Lean_Doc_Syntax_codeblock___closed__12();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__12);
l_Lean_Doc_Syntax_codeblock___closed__13 = _init_l_Lean_Doc_Syntax_codeblock___closed__13();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__13);
l_Lean_Doc_Syntax_codeblock___closed__14 = _init_l_Lean_Doc_Syntax_codeblock___closed__14();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock___closed__14);
l_Lean_Doc_Syntax_codeblock = _init_l_Lean_Doc_Syntax_codeblock();
lean_mark_persistent(l_Lean_Doc_Syntax_codeblock);
l_Lean_Doc_Syntax_blockquote___closed__0 = _init_l_Lean_Doc_Syntax_blockquote___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_blockquote___closed__0);
l_Lean_Doc_Syntax_blockquote___closed__1 = _init_l_Lean_Doc_Syntax_blockquote___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_blockquote___closed__1);
l_Lean_Doc_Syntax_blockquote___closed__2 = _init_l_Lean_Doc_Syntax_blockquote___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_blockquote___closed__2);
l_Lean_Doc_Syntax_blockquote___closed__3 = _init_l_Lean_Doc_Syntax_blockquote___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_blockquote___closed__3);
l_Lean_Doc_Syntax_blockquote___closed__4 = _init_l_Lean_Doc_Syntax_blockquote___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_blockquote___closed__4);
l_Lean_Doc_Syntax_blockquote___closed__5 = _init_l_Lean_Doc_Syntax_blockquote___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_blockquote___closed__5);
l_Lean_Doc_Syntax_blockquote = _init_l_Lean_Doc_Syntax_blockquote();
lean_mark_persistent(l_Lean_Doc_Syntax_blockquote);
l_Lean_Doc_Syntax_link__ref___closed__0 = _init_l_Lean_Doc_Syntax_link__ref___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_link__ref___closed__0);
l_Lean_Doc_Syntax_link__ref___closed__1 = _init_l_Lean_Doc_Syntax_link__ref___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_link__ref___closed__1);
l_Lean_Doc_Syntax_link__ref___closed__2 = _init_l_Lean_Doc_Syntax_link__ref___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_link__ref___closed__2);
l_Lean_Doc_Syntax_link__ref___closed__3 = _init_l_Lean_Doc_Syntax_link__ref___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_link__ref___closed__3);
l_Lean_Doc_Syntax_link__ref___closed__4 = _init_l_Lean_Doc_Syntax_link__ref___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_link__ref___closed__4);
l_Lean_Doc_Syntax_link__ref___closed__5 = _init_l_Lean_Doc_Syntax_link__ref___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_link__ref___closed__5);
l_Lean_Doc_Syntax_link__ref___closed__6 = _init_l_Lean_Doc_Syntax_link__ref___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_link__ref___closed__6);
l_Lean_Doc_Syntax_link__ref = _init_l_Lean_Doc_Syntax_link__ref();
lean_mark_persistent(l_Lean_Doc_Syntax_link__ref);
l_Lean_Doc_Syntax_footnote__ref___closed__0 = _init_l_Lean_Doc_Syntax_footnote__ref___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote__ref___closed__0);
l_Lean_Doc_Syntax_footnote__ref___closed__1 = _init_l_Lean_Doc_Syntax_footnote__ref___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote__ref___closed__1);
l_Lean_Doc_Syntax_footnote__ref___closed__2 = _init_l_Lean_Doc_Syntax_footnote__ref___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote__ref___closed__2);
l_Lean_Doc_Syntax_footnote__ref___closed__3 = _init_l_Lean_Doc_Syntax_footnote__ref___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote__ref___closed__3);
l_Lean_Doc_Syntax_footnote__ref___closed__4 = _init_l_Lean_Doc_Syntax_footnote__ref___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote__ref___closed__4);
l_Lean_Doc_Syntax_footnote__ref___closed__5 = _init_l_Lean_Doc_Syntax_footnote__ref___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote__ref___closed__5);
l_Lean_Doc_Syntax_footnote__ref___closed__6 = _init_l_Lean_Doc_Syntax_footnote__ref___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote__ref___closed__6);
l_Lean_Doc_Syntax_footnote__ref___closed__7 = _init_l_Lean_Doc_Syntax_footnote__ref___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote__ref___closed__7);
l_Lean_Doc_Syntax_footnote__ref = _init_l_Lean_Doc_Syntax_footnote__ref();
lean_mark_persistent(l_Lean_Doc_Syntax_footnote__ref);
l_Lean_Doc_Syntax_directive___closed__0 = _init_l_Lean_Doc_Syntax_directive___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__0);
l_Lean_Doc_Syntax_directive___closed__1 = _init_l_Lean_Doc_Syntax_directive___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__1);
l_Lean_Doc_Syntax_directive___closed__2 = _init_l_Lean_Doc_Syntax_directive___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__2);
l_Lean_Doc_Syntax_directive___closed__3 = _init_l_Lean_Doc_Syntax_directive___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__3);
l_Lean_Doc_Syntax_directive___closed__4 = _init_l_Lean_Doc_Syntax_directive___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__4);
l_Lean_Doc_Syntax_directive___closed__5 = _init_l_Lean_Doc_Syntax_directive___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__5);
l_Lean_Doc_Syntax_directive___closed__6 = _init_l_Lean_Doc_Syntax_directive___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__6);
l_Lean_Doc_Syntax_directive___closed__7 = _init_l_Lean_Doc_Syntax_directive___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__7);
l_Lean_Doc_Syntax_directive___closed__8 = _init_l_Lean_Doc_Syntax_directive___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__8);
l_Lean_Doc_Syntax_directive___closed__9 = _init_l_Lean_Doc_Syntax_directive___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__9);
l_Lean_Doc_Syntax_directive___closed__10 = _init_l_Lean_Doc_Syntax_directive___closed__10();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__10);
l_Lean_Doc_Syntax_directive___closed__11 = _init_l_Lean_Doc_Syntax_directive___closed__11();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__11);
l_Lean_Doc_Syntax_directive___closed__12 = _init_l_Lean_Doc_Syntax_directive___closed__12();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__12);
l_Lean_Doc_Syntax_directive___closed__13 = _init_l_Lean_Doc_Syntax_directive___closed__13();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__13);
l_Lean_Doc_Syntax_directive___closed__14 = _init_l_Lean_Doc_Syntax_directive___closed__14();
lean_mark_persistent(l_Lean_Doc_Syntax_directive___closed__14);
l_Lean_Doc_Syntax_directive = _init_l_Lean_Doc_Syntax_directive();
lean_mark_persistent(l_Lean_Doc_Syntax_directive);
l_Lean_Doc_Syntax_header___closed__0 = _init_l_Lean_Doc_Syntax_header___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_header___closed__0);
l_Lean_Doc_Syntax_header___closed__1 = _init_l_Lean_Doc_Syntax_header___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_header___closed__1);
l_Lean_Doc_Syntax_header___closed__2 = _init_l_Lean_Doc_Syntax_header___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_header___closed__2);
l_Lean_Doc_Syntax_header___closed__3 = _init_l_Lean_Doc_Syntax_header___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_header___closed__3);
l_Lean_Doc_Syntax_header___closed__4 = _init_l_Lean_Doc_Syntax_header___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_header___closed__4);
l_Lean_Doc_Syntax_header___closed__5 = _init_l_Lean_Doc_Syntax_header___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_header___closed__5);
l_Lean_Doc_Syntax_header___closed__6 = _init_l_Lean_Doc_Syntax_header___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_header___closed__6);
l_Lean_Doc_Syntax_header___closed__7 = _init_l_Lean_Doc_Syntax_header___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_header___closed__7);
l_Lean_Doc_Syntax_header___closed__8 = _init_l_Lean_Doc_Syntax_header___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_header___closed__8);
l_Lean_Doc_Syntax_header___closed__9 = _init_l_Lean_Doc_Syntax_header___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_header___closed__9);
l_Lean_Doc_Syntax_header = _init_l_Lean_Doc_Syntax_header();
lean_mark_persistent(l_Lean_Doc_Syntax_header);
l_Lean_Doc_Syntax_metadataContents___closed__0 = _init_l_Lean_Doc_Syntax_metadataContents___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__0);
l_Lean_Doc_Syntax_metadataContents___closed__1 = _init_l_Lean_Doc_Syntax_metadataContents___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__1);
l_Lean_Doc_Syntax_metadataContents___closed__2 = _init_l_Lean_Doc_Syntax_metadataContents___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__2);
l_Lean_Doc_Syntax_metadataContents___closed__3 = _init_l_Lean_Doc_Syntax_metadataContents___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__3);
l_Lean_Doc_Syntax_metadataContents___closed__4 = _init_l_Lean_Doc_Syntax_metadataContents___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__4);
l_Lean_Doc_Syntax_metadataContents___closed__5 = _init_l_Lean_Doc_Syntax_metadataContents___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__5);
l_Lean_Doc_Syntax_metadataContents___closed__6 = _init_l_Lean_Doc_Syntax_metadataContents___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__6);
l_Lean_Doc_Syntax_metadataContents___closed__7 = _init_l_Lean_Doc_Syntax_metadataContents___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__7);
l_Lean_Doc_Syntax_metadataContents___closed__8 = _init_l_Lean_Doc_Syntax_metadataContents___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__8);
l_Lean_Doc_Syntax_metadataContents___closed__9 = _init_l_Lean_Doc_Syntax_metadataContents___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__9);
l_Lean_Doc_Syntax_metadataContents___closed__10 = _init_l_Lean_Doc_Syntax_metadataContents___closed__10();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__10);
l_Lean_Doc_Syntax_metadataContents___closed__11 = _init_l_Lean_Doc_Syntax_metadataContents___closed__11();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__11);
l_Lean_Doc_Syntax_metadataContents___closed__12 = _init_l_Lean_Doc_Syntax_metadataContents___closed__12();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__12);
l_Lean_Doc_Syntax_metadataContents___closed__13 = _init_l_Lean_Doc_Syntax_metadataContents___closed__13();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__13);
l_Lean_Doc_Syntax_metadataContents___closed__14 = _init_l_Lean_Doc_Syntax_metadataContents___closed__14();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__14);
l_Lean_Doc_Syntax_metadataContents___closed__15 = _init_l_Lean_Doc_Syntax_metadataContents___closed__15();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__15);
l_Lean_Doc_Syntax_metadataContents___closed__16 = _init_l_Lean_Doc_Syntax_metadataContents___closed__16();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__16);
l_Lean_Doc_Syntax_metadataContents___closed__17 = _init_l_Lean_Doc_Syntax_metadataContents___closed__17();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__17);
l_Lean_Doc_Syntax_metadataContents___closed__18 = _init_l_Lean_Doc_Syntax_metadataContents___closed__18();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__18);
l_Lean_Doc_Syntax_metadataContents___closed__19 = _init_l_Lean_Doc_Syntax_metadataContents___closed__19();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents___closed__19);
l_Lean_Doc_Syntax_metadataContents = _init_l_Lean_Doc_Syntax_metadataContents();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents);
l_Lean_Doc_Syntax_metadata__block___closed__0 = _init_l_Lean_Doc_Syntax_metadata__block___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block___closed__0);
l_Lean_Doc_Syntax_metadata__block___closed__1 = _init_l_Lean_Doc_Syntax_metadata__block___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block___closed__1);
l_Lean_Doc_Syntax_metadata__block___closed__2 = _init_l_Lean_Doc_Syntax_metadata__block___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block___closed__2);
l_Lean_Doc_Syntax_metadata__block___closed__3 = _init_l_Lean_Doc_Syntax_metadata__block___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block___closed__3);
l_Lean_Doc_Syntax_metadata__block___closed__4 = _init_l_Lean_Doc_Syntax_metadata__block___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block___closed__4);
l_Lean_Doc_Syntax_metadata__block___closed__5 = _init_l_Lean_Doc_Syntax_metadata__block___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block___closed__5);
l_Lean_Doc_Syntax_metadata__block___closed__6 = _init_l_Lean_Doc_Syntax_metadata__block___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block___closed__6);
l_Lean_Doc_Syntax_metadata__block___closed__7 = _init_l_Lean_Doc_Syntax_metadata__block___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block___closed__7);
l_Lean_Doc_Syntax_metadata__block___closed__8 = _init_l_Lean_Doc_Syntax_metadata__block___closed__8();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block___closed__8);
l_Lean_Doc_Syntax_metadata__block___closed__9 = _init_l_Lean_Doc_Syntax_metadata__block___closed__9();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block___closed__9);
l_Lean_Doc_Syntax_metadata__block = _init_l_Lean_Doc_Syntax_metadata__block();
lean_mark_persistent(l_Lean_Doc_Syntax_metadata__block);
l_Lean_Doc_Syntax_metadataContents_formatter___closed__0 = _init_l_Lean_Doc_Syntax_metadataContents_formatter___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents_formatter___closed__0);
l_Lean_Doc_Syntax_metadataContents_formatter___closed__1 = _init_l_Lean_Doc_Syntax_metadataContents_formatter___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents_formatter___closed__1);
l_Lean_Doc_Syntax_metadataContents_formatter___closed__2 = _init_l_Lean_Doc_Syntax_metadataContents_formatter___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents_formatter___closed__2);
l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0 = _init_l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0);
l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1 = _init_l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1);
l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2 = _init_l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2);
l_Lean_Doc_Syntax_command___closed__0 = _init_l_Lean_Doc_Syntax_command___closed__0();
lean_mark_persistent(l_Lean_Doc_Syntax_command___closed__0);
l_Lean_Doc_Syntax_command___closed__1 = _init_l_Lean_Doc_Syntax_command___closed__1();
lean_mark_persistent(l_Lean_Doc_Syntax_command___closed__1);
l_Lean_Doc_Syntax_command___closed__2 = _init_l_Lean_Doc_Syntax_command___closed__2();
lean_mark_persistent(l_Lean_Doc_Syntax_command___closed__2);
l_Lean_Doc_Syntax_command___closed__3 = _init_l_Lean_Doc_Syntax_command___closed__3();
lean_mark_persistent(l_Lean_Doc_Syntax_command___closed__3);
l_Lean_Doc_Syntax_command___closed__4 = _init_l_Lean_Doc_Syntax_command___closed__4();
lean_mark_persistent(l_Lean_Doc_Syntax_command___closed__4);
l_Lean_Doc_Syntax_command___closed__5 = _init_l_Lean_Doc_Syntax_command___closed__5();
lean_mark_persistent(l_Lean_Doc_Syntax_command___closed__5);
l_Lean_Doc_Syntax_command___closed__6 = _init_l_Lean_Doc_Syntax_command___closed__6();
lean_mark_persistent(l_Lean_Doc_Syntax_command___closed__6);
l_Lean_Doc_Syntax_command___closed__7 = _init_l_Lean_Doc_Syntax_command___closed__7();
lean_mark_persistent(l_Lean_Doc_Syntax_command___closed__7);
l_Lean_Doc_Syntax_command = _init_l_Lean_Doc_Syntax_command();
lean_mark_persistent(l_Lean_Doc_Syntax_command);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
