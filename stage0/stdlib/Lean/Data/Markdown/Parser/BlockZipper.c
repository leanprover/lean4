// Lean compiler output
// Module: Lean.Data.Markdown.Parser.BlockZipper
// Imports: import Init public import Lean.Data.Markdown.Block public import Lean.Data.Markdown.Parser.Html public import Lean.Data.Markdown.Parser.Children import Lean.Data.Markdown.InlineSource
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
lean_object* l_Lean_Markdown_InlineSource_ofLines(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Markdown_Children_push(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Markdown_Children_flushLists(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_Children_setPendingList(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Markdown_Children_empty___redArg();
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Markdown_Lines_singleton___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_Children_takePendingList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_blockquote_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_blockquote_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_blockquote_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_listItem_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_listItem_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_listItem_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Markdown_instInhabitedOpenContainer_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default___redArg___closed__0 = (const lean_object*)&l_Lean_Markdown_instInhabitedOpenContainer_default___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_instInhabitedOpenContainer_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Markdown_instInhabitedOpenContainer_default___redArg___closed__0_value)}};
static const lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default___redArg___closed__1 = (const lean_object*)&l_Lean_Markdown_instInhabitedOpenContainer_default___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer___boxed(lean_object*);
static lean_once_cell_t l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0;
static lean_once_cell_t l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_paragraph_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_paragraph_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_paragraph_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_fencedCode_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_fencedCode_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_fencedCode_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_indentedCode_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_indentedCode_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_indentedCode_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_html_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_html_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_html_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenLeaf_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenLeaf_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenLeaf(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenLeaf___boxed(lean_object*);
static const lean_array_object l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__0 = (const lean_object*)&l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Markdown_BlockZipper_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_BlockZipper_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_top_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_top_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_top_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_top_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_leafToBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_leafToBlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyChildren___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyChildren(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyChildren___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyGetChildren___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyGetChildren(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyGetChildren___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushChild(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushChild___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeLeaf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeLeaf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_listLikeFloor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_listLikeFloor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_recordBlankLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_recordBlankLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_recordContentLine___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_recordContentLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_recordContentLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeContainer(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeContainer___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openBlockquote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openBlockquote___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Markdown_BlockZipper_openItem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Markdown_BlockZipper_openItem___closed__0 = (const lean_object*)&l_Lean_Markdown_BlockZipper_openItem___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openLeaf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openLeaf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_addBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_addBlock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyLeaf___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyLeaf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyLeaf___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendParagraph___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendParagraph(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendParagraph___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendFencedCode___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendFencedCode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendFencedCode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendHtml___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendHtml(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendHtml___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeFencedCode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeFencedCode___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Markdown_BlockZipper_indentedCodeAddLine___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddLine___redArg___closed__0 = (const lean_object*)&l_Lean_Markdown_BlockZipper_indentedCodeAddLine___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddLine___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddLine(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddLine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddBlank___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddBlank(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddBlank___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_pushBlockquoteMarker___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_pushBlockquoteMarker___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_pushBlockquoteMarker(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_pushBlockquoteMarker___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushBlockquoteMarker_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushBlockquoteMarker_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushBlockquoteMarker_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_finalize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_finalize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Markdown_OpenContainer_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorIdx___impl(lean_object* v_s_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorIdx___impl___boxed(lean_object* v_s_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Markdown_OpenContainer_ctorIdx___impl(v_s_8_, v_x_9_);
lean_dec_ref(v_x_9_);
lean_dec_ref(v_s_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
if (lean_obj_tag(v_t_11_) == 0)
{
lean_object* v_markers_13_; lean_object* v___x_14_; 
v_markers_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_markers_13_);
lean_dec_ref_known(v_t_11_, 1);
v___x_14_ = lean_apply_1(v_k_12_, v_markers_13_);
return v___x_14_;
}
else
{
lean_object* v_list_15_; lean_object* v_marker_16_; lean_object* v_contentColumn_17_; lean_object* v___x_18_; 
v_list_15_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_list_15_);
v_marker_16_ = lean_ctor_get(v_t_11_, 1);
lean_inc_ref(v_marker_16_);
v_contentColumn_17_ = lean_ctor_get(v_t_11_, 2);
lean_inc(v_contentColumn_17_);
lean_dec_ref_known(v_t_11_, 3);
v___x_18_ = lean_apply_3(v_k_12_, v_list_15_, v_marker_16_, v_contentColumn_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorElim(lean_object* v_s_19_, lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Markdown_OpenContainer_ctorElim___redArg(v_t_22_, v_k_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_ctorElim___boxed(lean_object* v_s_26_, lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Markdown_OpenContainer_ctorElim(v_s_26_, v_motive_27_, v_ctorIdx_28_, v_t_29_, v_h_30_, v_k_31_);
lean_dec(v_ctorIdx_28_);
lean_dec_ref(v_s_26_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_blockquote_elim___redArg(lean_object* v_t_33_, lean_object* v_blockquote_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Markdown_OpenContainer_ctorElim___redArg(v_t_33_, v_blockquote_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_blockquote_elim(lean_object* v_s_36_, lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_blockquote_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Markdown_OpenContainer_ctorElim___redArg(v_t_38_, v_blockquote_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_blockquote_elim___boxed(lean_object* v_s_42_, lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_blockquote_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Markdown_OpenContainer_blockquote_elim(v_s_42_, v_motive_43_, v_t_44_, v_h_45_, v_blockquote_46_);
lean_dec_ref(v_s_42_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_listItem_elim___redArg(lean_object* v_t_48_, lean_object* v_listItem_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Markdown_OpenContainer_ctorElim___redArg(v_t_48_, v_listItem_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_listItem_elim(lean_object* v_s_51_, lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_listItem_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Markdown_OpenContainer_ctorElim___redArg(v_t_53_, v_listItem_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenContainer_listItem_elim___boxed(lean_object* v_s_57_, lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_listItem_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Markdown_OpenContainer_listItem_elim(v_s_57_, v_motive_58_, v_t_59_, v_h_60_, v_listItem_61_);
lean_dec_ref(v_s_57_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default___redArg(){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = ((lean_object*)(l_Lean_Markdown_instInhabitedOpenContainer_default___redArg___closed__1));
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default___redArg___boxed(lean_object* v___dummy_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Markdown_instInhabitedOpenContainer_default___redArg();
return v_res_70_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Markdown_instInhabitedOpenContainer_default___redArg();
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default(lean_object* v_s_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_obj_once(&l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0, &l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer_default___boxed(lean_object* v_s_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Markdown_instInhabitedOpenContainer_default(v_s_74_);
lean_dec_ref(v_s_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer___redArg(){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0, &l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer___redArg___boxed(lean_object* v___dummy_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Markdown_instInhabitedOpenContainer___redArg();
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer(lean_object* v_a_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0, &l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenContainer___boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Markdown_instInhabitedOpenContainer(v_a_82_);
lean_dec_ref(v_a_82_);
return v_res_83_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Markdown_Children_empty___redArg();
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_obj_once(&l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0, &l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0_once, _init_l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0);
v___x_86_ = lean_obj_once(&l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0, &l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedOpenContainer_default___closed__0);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default___redArg(){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__1, &l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__1_once, _init_l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__1);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___boxed(lean_object* v___dummy_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Markdown_instInhabitedZipperFrame_default___redArg();
return v_res_91_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Markdown_instInhabitedZipperFrame_default___redArg();
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default(lean_object* v_s_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0, &l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame_default___boxed(lean_object* v_s_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Markdown_instInhabitedZipperFrame_default(v_s_95_);
lean_dec_ref(v_s_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame___redArg(){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0, &l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame___redArg___boxed(lean_object* v___dummy_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Markdown_instInhabitedZipperFrame___redArg();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame(lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0, &l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedZipperFrame_default___closed__0);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedZipperFrame___boxed(lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Markdown_instInhabitedZipperFrame(v_a_103_);
lean_dec_ref(v_a_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorIdx___impl___redArg(lean_object* v_x_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_tag_nat(v_x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorIdx___impl___redArg___boxed(lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Markdown_OpenLeaf_ctorIdx___impl___redArg(v_x_107_);
lean_dec_ref(v_x_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorIdx___impl(lean_object* v_s_109_, lean_object* v_x_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = lean_obj_tag_nat(v_x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorIdx___impl___boxed(lean_object* v_s_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Markdown_OpenLeaf_ctorIdx___impl(v_s_112_, v_x_113_);
lean_dec_ref(v_x_113_);
lean_dec_ref(v_s_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorElim___redArg(lean_object* v_t_115_, lean_object* v_k_116_){
_start:
{
switch(lean_obj_tag(v_t_115_))
{
case 0:
{
lean_object* v_lines_117_; lean_object* v___x_118_; 
v_lines_117_ = lean_ctor_get(v_t_115_, 0);
lean_inc_ref(v_lines_117_);
lean_dec_ref_known(v_t_115_, 1);
v___x_118_ = lean_apply_1(v_k_116_, v_lines_117_);
return v___x_118_;
}
case 1:
{
lean_object* v_info_119_; lean_object* v_openFence_120_; lean_object* v_lines_121_; lean_object* v___x_122_; 
v_info_119_ = lean_ctor_get(v_t_115_, 0);
lean_inc_ref(v_info_119_);
v_openFence_120_ = lean_ctor_get(v_t_115_, 1);
lean_inc_ref(v_openFence_120_);
v_lines_121_ = lean_ctor_get(v_t_115_, 2);
lean_inc_ref(v_lines_121_);
lean_dec_ref_known(v_t_115_, 3);
v___x_122_ = lean_apply_3(v_k_116_, v_info_119_, v_openFence_120_, v_lines_121_);
return v___x_122_;
}
case 2:
{
lean_object* v_lines_123_; lean_object* v_pendingBlanks_124_; lean_object* v___x_125_; 
v_lines_123_ = lean_ctor_get(v_t_115_, 0);
lean_inc_ref(v_lines_123_);
v_pendingBlanks_124_ = lean_ctor_get(v_t_115_, 1);
lean_inc_ref(v_pendingBlanks_124_);
lean_dec_ref_known(v_t_115_, 2);
v___x_125_ = lean_apply_2(v_k_116_, v_lines_123_, v_pendingBlanks_124_);
return v___x_125_;
}
default: 
{
uint8_t v_kind_126_; lean_object* v_lines_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_kind_126_ = lean_ctor_get_uint8(v_t_115_, sizeof(void*)*1);
v_lines_127_ = lean_ctor_get(v_t_115_, 0);
lean_inc_ref(v_lines_127_);
lean_dec_ref_known(v_t_115_, 1);
v___x_128_ = lean_box(v_kind_126_);
v___x_129_ = lean_apply_2(v_k_116_, v___x_128_, v_lines_127_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorElim(lean_object* v_s_130_, lean_object* v_motive_131_, lean_object* v_ctorIdx_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_k_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Markdown_OpenLeaf_ctorElim___redArg(v_t_133_, v_k_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_ctorElim___boxed(lean_object* v_s_137_, lean_object* v_motive_138_, lean_object* v_ctorIdx_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_k_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Markdown_OpenLeaf_ctorElim(v_s_137_, v_motive_138_, v_ctorIdx_139_, v_t_140_, v_h_141_, v_k_142_);
lean_dec(v_ctorIdx_139_);
lean_dec_ref(v_s_137_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_paragraph_elim___redArg(lean_object* v_t_144_, lean_object* v_paragraph_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Markdown_OpenLeaf_ctorElim___redArg(v_t_144_, v_paragraph_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_paragraph_elim(lean_object* v_s_147_, lean_object* v_motive_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_paragraph_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Markdown_OpenLeaf_ctorElim___redArg(v_t_149_, v_paragraph_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_paragraph_elim___boxed(lean_object* v_s_153_, lean_object* v_motive_154_, lean_object* v_t_155_, lean_object* v_h_156_, lean_object* v_paragraph_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Markdown_OpenLeaf_paragraph_elim(v_s_153_, v_motive_154_, v_t_155_, v_h_156_, v_paragraph_157_);
lean_dec_ref(v_s_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_fencedCode_elim___redArg(lean_object* v_t_159_, lean_object* v_fencedCode_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Markdown_OpenLeaf_ctorElim___redArg(v_t_159_, v_fencedCode_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_fencedCode_elim(lean_object* v_s_162_, lean_object* v_motive_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_fencedCode_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Markdown_OpenLeaf_ctorElim___redArg(v_t_164_, v_fencedCode_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_fencedCode_elim___boxed(lean_object* v_s_168_, lean_object* v_motive_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_fencedCode_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Markdown_OpenLeaf_fencedCode_elim(v_s_168_, v_motive_169_, v_t_170_, v_h_171_, v_fencedCode_172_);
lean_dec_ref(v_s_168_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_indentedCode_elim___redArg(lean_object* v_t_174_, lean_object* v_indentedCode_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Markdown_OpenLeaf_ctorElim___redArg(v_t_174_, v_indentedCode_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_indentedCode_elim(lean_object* v_s_177_, lean_object* v_motive_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_indentedCode_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Markdown_OpenLeaf_ctorElim___redArg(v_t_179_, v_indentedCode_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_indentedCode_elim___boxed(lean_object* v_s_183_, lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_indentedCode_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Markdown_OpenLeaf_indentedCode_elim(v_s_183_, v_motive_184_, v_t_185_, v_h_186_, v_indentedCode_187_);
lean_dec_ref(v_s_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_html_elim___redArg(lean_object* v_t_189_, lean_object* v_html_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Markdown_OpenLeaf_ctorElim___redArg(v_t_189_, v_html_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_html_elim(lean_object* v_s_192_, lean_object* v_motive_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_html_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Markdown_OpenLeaf_ctorElim___redArg(v_t_194_, v_html_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_OpenLeaf_html_elim___boxed(lean_object* v_s_198_, lean_object* v_motive_199_, lean_object* v_t_200_, lean_object* v_h_201_, lean_object* v_html_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Markdown_OpenLeaf_html_elim(v_s_198_, v_motive_199_, v_t_200_, v_h_201_, v_html_202_);
lean_dec_ref(v_s_198_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenLeaf_default(lean_object* v_s_204_){
_start:
{
lean_object* v_startInclusive_205_; lean_object* v_endExclusive_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_startInclusive_205_ = lean_ctor_get(v_s_204_, 1);
v_endExclusive_206_ = lean_ctor_get(v_s_204_, 2);
v___x_207_ = lean_nat_sub(v_endExclusive_206_, v_startInclusive_205_);
lean_inc(v___x_207_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenLeaf_default___boxed(lean_object* v_s_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Markdown_instInhabitedOpenLeaf_default(v_s_211_);
lean_dec_ref(v_s_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenLeaf(lean_object* v_a_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Markdown_instInhabitedOpenLeaf_default(v_a_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenLeaf___boxed(lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Markdown_instInhabitedOpenLeaf(v_a_215_);
lean_dec_ref(v_a_215_);
return v_res_216_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_219_ = lean_box(0);
v___x_220_ = ((lean_object*)(l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__0));
v___x_221_ = lean_obj_once(&l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0, &l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0_once, _init_l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0);
v___x_222_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_219_);
lean_ctor_set(v___x_222_, 3, v___x_219_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default___redArg(){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_obj_once(&l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__1, &l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__1_once, _init_l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__1);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___boxed(lean_object* v___dummy_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Markdown_instInhabitedBlockZipper_default___redArg();
return v_res_226_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0(void){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Markdown_instInhabitedBlockZipper_default___redArg();
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default(lean_object* v_s_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_obj_once(&l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0, &l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper_default___boxed(lean_object* v_s_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Markdown_instInhabitedBlockZipper_default(v_s_230_);
lean_dec_ref(v_s_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper___redArg(){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0, &l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper___redArg___boxed(lean_object* v___dummy_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Markdown_instInhabitedBlockZipper___redArg();
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper(lean_object* v_a_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_obj_once(&l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0, &l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedBlockZipper_default___closed__0);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedBlockZipper___boxed(lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Markdown_instInhabitedBlockZipper(v_a_238_);
lean_dec_ref(v_a_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_empty___redArg(){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__1, &l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__1_once, _init_l_Lean_Markdown_instInhabitedBlockZipper_default___redArg___closed__1);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_empty___redArg___boxed(lean_object* v___dummy_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Markdown_BlockZipper_empty___redArg();
return v_res_243_;
}
}
static lean_object* _init_l_Lean_Markdown_BlockZipper_empty___closed__0(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Markdown_BlockZipper_empty___redArg();
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_empty(lean_object* v_s_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Lean_Markdown_BlockZipper_empty___closed__0, &l_Lean_Markdown_BlockZipper_empty___closed__0_once, _init_l_Lean_Markdown_BlockZipper_empty___closed__0);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_empty___boxed(lean_object* v_s_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Markdown_BlockZipper_empty(v_s_247_);
lean_dec_ref(v_s_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_top_x3f___redArg(lean_object* v_z_249_){
_start:
{
lean_object* v_spine_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_spine_250_ = lean_ctor_get(v_z_249_, 1);
v___x_251_ = lean_array_get_size(v_spine_250_);
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_nat_sub(v___x_251_, v___x_252_);
v___x_254_ = lean_nat_dec_lt(v___x_253_, v___x_251_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v___x_253_);
v___x_255_ = lean_box(0);
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v_container_257_; lean_object* v___x_258_; 
v___x_256_ = lean_array_fget_borrowed(v_spine_250_, v___x_253_);
lean_dec(v___x_253_);
v_container_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc_ref(v_container_257_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_container_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_top_x3f___redArg___boxed(lean_object* v_z_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Markdown_BlockZipper_top_x3f___redArg(v_z_259_);
lean_dec_ref(v_z_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_top_x3f(lean_object* v_s_261_, lean_object* v_z_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Markdown_BlockZipper_top_x3f___redArg(v_z_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_top_x3f___boxed(lean_object* v_s_264_, lean_object* v_z_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Markdown_BlockZipper_top_x3f(v_s_264_, v_z_265_);
lean_dec_ref(v_z_265_);
lean_dec_ref(v_s_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_leafToBlock(lean_object* v_s_267_, lean_object* v_x_268_){
_start:
{
switch(lean_obj_tag(v_x_268_))
{
case 0:
{
lean_object* v_lines_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_lines_269_ = lean_ctor_get(v_x_268_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v_x_268_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_lines_269_);
lean_dec(v_x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = l_Lean_Markdown_InlineSource_ofLines(v_s_267_, v_lines_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
case 1:
{
lean_object* v_info_278_; lean_object* v_openFence_279_; lean_object* v_lines_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_info_278_ = lean_ctor_get(v_x_268_, 0);
lean_inc_ref(v_info_278_);
v_openFence_279_ = lean_ctor_get(v_x_268_, 1);
lean_inc_ref(v_openFence_279_);
v_lines_280_ = lean_ctor_get(v_x_268_, 2);
lean_inc_ref(v_lines_280_);
lean_dec_ref_known(v_x_268_, 3);
v___x_281_ = lean_box(0);
v___x_282_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_282_, 0, v_info_278_);
lean_ctor_set(v___x_282_, 1, v_openFence_279_);
lean_ctor_set(v___x_282_, 2, v___x_281_);
lean_ctor_set(v___x_282_, 3, v_lines_280_);
return v___x_282_;
}
case 2:
{
lean_object* v_lines_283_; lean_object* v___x_284_; 
v_lines_283_ = lean_ctor_get(v_x_268_, 0);
lean_inc_ref(v_lines_283_);
lean_dec_ref_known(v_x_268_, 2);
v___x_284_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_284_, 0, v_lines_283_);
return v___x_284_;
}
default: 
{
lean_object* v_lines_285_; lean_object* v___x_286_; 
v_lines_285_ = lean_ctor_get(v_x_268_, 0);
lean_inc_ref(v_lines_285_);
lean_dec_ref_known(v_x_268_, 1);
v___x_286_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_286_, 0, v_lines_285_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_leafToBlock___boxed(lean_object* v_s_287_, lean_object* v_x_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Markdown_BlockZipper_leafToBlock(v_s_287_, v_x_288_);
lean_dec_ref(v_s_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyChildren___redArg(lean_object* v_z_290_, lean_object* v_f_291_){
_start:
{
lean_object* v_document_292_; lean_object* v_spine_293_; lean_object* v_openLeaf_x3f_294_; lean_object* v_blankLineFloor_x3f_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_329_; 
v_document_292_ = lean_ctor_get(v_z_290_, 0);
v_spine_293_ = lean_ctor_get(v_z_290_, 1);
v_openLeaf_x3f_294_ = lean_ctor_get(v_z_290_, 2);
v_blankLineFloor_x3f_295_ = lean_ctor_get(v_z_290_, 3);
v_isSharedCheck_329_ = !lean_is_exclusive(v_z_290_);
if (v_isSharedCheck_329_ == 0)
{
v___x_297_ = v_z_290_;
v_isShared_298_ = v_isSharedCheck_329_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_blankLineFloor_x3f_295_);
lean_inc(v_openLeaf_x3f_294_);
lean_inc(v_spine_293_);
lean_inc(v_document_292_);
lean_dec(v_z_290_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_329_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_299_ = lean_array_get_size(v_spine_293_);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_nat_dec_eq(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_sub(v___x_299_, v___x_302_);
v___x_304_ = lean_nat_dec_lt(v___x_303_, v___x_299_);
if (v___x_304_ == 0)
{
lean_object* v___x_306_; 
lean_dec(v___x_303_);
lean_dec_ref(v_f_291_);
if (v_isShared_298_ == 0)
{
v___x_306_ = v___x_297_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_document_292_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_spine_293_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_openLeaf_x3f_294_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_blankLineFloor_x3f_295_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
else
{
lean_object* v_v_308_; lean_object* v_container_309_; lean_object* v_children_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_324_; 
v_v_308_ = lean_array_fget(v_spine_293_, v___x_303_);
v_container_309_ = lean_ctor_get(v_v_308_, 0);
v_children_310_ = lean_ctor_get(v_v_308_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v_v_308_);
if (v_isSharedCheck_324_ == 0)
{
v___x_312_ = v_v_308_;
v_isShared_313_ = v_isSharedCheck_324_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_children_310_);
lean_inc(v_container_309_);
lean_dec(v_v_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_324_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v_xs_x27_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_314_ = lean_box(0);
v_xs_x27_315_ = lean_array_fset(v_spine_293_, v___x_303_, v___x_314_);
v___x_316_ = lean_apply_1(v_f_291_, v_children_310_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_316_);
v___x_318_ = v___x_312_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_container_309_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_323_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = lean_array_fset(v_xs_x27_315_, v___x_303_, v___x_318_);
lean_dec(v___x_303_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v___x_319_);
v___x_321_ = v___x_297_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_document_292_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_openLeaf_x3f_294_);
lean_ctor_set(v_reuseFailAlloc_322_, 3, v_blankLineFloor_x3f_295_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
else
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_apply_1(v_f_291_, v_document_292_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_325_);
v___x_327_ = v___x_297_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_spine_293_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_openLeaf_x3f_294_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v_blankLineFloor_x3f_295_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyChildren(lean_object* v_s_330_, lean_object* v_z_331_, lean_object* v_f_332_){
_start:
{
lean_object* v_document_333_; lean_object* v_spine_334_; lean_object* v_openLeaf_x3f_335_; lean_object* v_blankLineFloor_x3f_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_370_; 
v_document_333_ = lean_ctor_get(v_z_331_, 0);
v_spine_334_ = lean_ctor_get(v_z_331_, 1);
v_openLeaf_x3f_335_ = lean_ctor_get(v_z_331_, 2);
v_blankLineFloor_x3f_336_ = lean_ctor_get(v_z_331_, 3);
v_isSharedCheck_370_ = !lean_is_exclusive(v_z_331_);
if (v_isSharedCheck_370_ == 0)
{
v___x_338_ = v_z_331_;
v_isShared_339_ = v_isSharedCheck_370_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_blankLineFloor_x3f_336_);
lean_inc(v_openLeaf_x3f_335_);
lean_inc(v_spine_334_);
lean_inc(v_document_333_);
lean_dec(v_z_331_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_370_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_array_get_size(v_spine_334_);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_nat_dec_eq(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_sub(v___x_340_, v___x_343_);
v___x_345_ = lean_nat_dec_lt(v___x_344_, v___x_340_);
if (v___x_345_ == 0)
{
lean_object* v___x_347_; 
lean_dec(v___x_344_);
lean_dec_ref(v_f_332_);
if (v_isShared_339_ == 0)
{
v___x_347_ = v___x_338_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_document_333_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_spine_334_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v_openLeaf_x3f_335_);
lean_ctor_set(v_reuseFailAlloc_348_, 3, v_blankLineFloor_x3f_336_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
else
{
lean_object* v_v_349_; lean_object* v_container_350_; lean_object* v_children_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_365_; 
v_v_349_ = lean_array_fget(v_spine_334_, v___x_344_);
v_container_350_ = lean_ctor_get(v_v_349_, 0);
v_children_351_ = lean_ctor_get(v_v_349_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_v_349_);
if (v_isSharedCheck_365_ == 0)
{
v___x_353_ = v_v_349_;
v_isShared_354_ = v_isSharedCheck_365_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_children_351_);
lean_inc(v_container_350_);
lean_dec(v_v_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_365_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v_xs_x27_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_355_ = lean_box(0);
v_xs_x27_356_ = lean_array_fset(v_spine_334_, v___x_344_, v___x_355_);
v___x_357_ = lean_apply_1(v_f_332_, v_children_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_357_);
v___x_359_ = v___x_353_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_container_350_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v___x_357_);
v___x_359_ = v_reuseFailAlloc_364_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_array_fset(v_xs_x27_356_, v___x_344_, v___x_359_);
lean_dec(v___x_344_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v___x_360_);
v___x_362_ = v___x_338_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_document_333_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_openLeaf_x3f_335_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v_blankLineFloor_x3f_336_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = lean_apply_1(v_f_332_, v_document_333_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_366_);
v___x_368_ = v___x_338_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_spine_334_);
lean_ctor_set(v_reuseFailAlloc_369_, 2, v_openLeaf_x3f_335_);
lean_ctor_set(v_reuseFailAlloc_369_, 3, v_blankLineFloor_x3f_336_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyChildren___boxed(lean_object* v_s_371_, lean_object* v_z_372_, lean_object* v_f_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyChildren(v_s_371_, v_z_372_, v_f_373_);
lean_dec_ref(v_s_371_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyGetChildren___redArg(lean_object* v_z_375_, lean_object* v_f_376_){
_start:
{
lean_object* v_document_377_; lean_object* v_spine_378_; lean_object* v_openLeaf_x3f_379_; lean_object* v_blankLineFloor_x3f_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_427_; 
v_document_377_ = lean_ctor_get(v_z_375_, 0);
v_spine_378_ = lean_ctor_get(v_z_375_, 1);
v_openLeaf_x3f_379_ = lean_ctor_get(v_z_375_, 2);
v_blankLineFloor_x3f_380_ = lean_ctor_get(v_z_375_, 3);
v_isSharedCheck_427_ = !lean_is_exclusive(v_z_375_);
if (v_isSharedCheck_427_ == 0)
{
v___x_382_ = v_z_375_;
v_isShared_383_ = v_isSharedCheck_427_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_blankLineFloor_x3f_380_);
lean_inc(v_openLeaf_x3f_379_);
lean_inc(v_spine_378_);
lean_inc(v_document_377_);
lean_dec(v_z_375_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_427_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_array_get_size(v_spine_378_);
v___x_386_ = lean_nat_dec_lt(v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; lean_object* v_fst_388_; lean_object* v_snd_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_399_; 
v___x_387_ = lean_apply_1(v_f_376_, v_document_377_);
v_fst_388_ = lean_ctor_get(v___x_387_, 0);
v_snd_389_ = lean_ctor_get(v___x_387_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_399_ == 0)
{
v___x_391_ = v___x_387_;
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_snd_389_);
lean_inc(v_fst_388_);
lean_dec(v___x_387_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v_fst_388_);
v___x_394_ = v___x_382_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_fst_388_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_spine_378_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_openLeaf_x3f_379_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_blankLineFloor_x3f_380_);
v___x_394_ = v_reuseFailAlloc_398_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_394_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_snd_389_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_frame_402_; lean_object* v_container_403_; lean_object* v_children_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_426_; 
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_sub(v___x_385_, v___x_400_);
v_frame_402_ = lean_array_fget(v_spine_378_, v___x_401_);
lean_dec(v___x_401_);
v_container_403_ = lean_ctor_get(v_frame_402_, 0);
v_children_404_ = lean_ctor_get(v_frame_402_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v_frame_402_);
if (v_isSharedCheck_426_ == 0)
{
v___x_406_ = v_frame_402_;
v_isShared_407_ = v_isSharedCheck_426_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_children_404_);
lean_inc(v_container_403_);
lean_dec(v_frame_402_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_426_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v_fst_409_; lean_object* v_snd_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_425_; 
v___x_408_ = lean_apply_1(v_f_376_, v_children_404_);
v_fst_409_ = lean_ctor_get(v___x_408_, 0);
v_snd_410_ = lean_ctor_get(v___x_408_, 1);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_425_ == 0)
{
v___x_412_ = v___x_408_;
v_isShared_413_ = v_isSharedCheck_425_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_snd_410_);
lean_inc(v_fst_409_);
lean_dec(v___x_408_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_425_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_spine_414_; lean_object* v___x_416_; 
v_spine_414_ = lean_array_pop(v_spine_378_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_fst_409_);
v___x_416_ = v___x_406_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_container_403_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_fst_409_);
v___x_416_ = v_reuseFailAlloc_424_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_array_push(v_spine_414_, v___x_416_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v___x_417_);
v___x_419_ = v___x_382_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_document_377_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_openLeaf_x3f_379_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_blankLineFloor_x3f_380_);
v___x_419_ = v_reuseFailAlloc_423_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_421_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_419_);
v___x_421_ = v___x_412_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_snd_410_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyGetChildren(lean_object* v_s_428_, lean_object* v_00_u03b1_429_, lean_object* v_z_430_, lean_object* v_f_431_){
_start:
{
lean_object* v_document_432_; lean_object* v_spine_433_; lean_object* v_openLeaf_x3f_434_; lean_object* v_blankLineFloor_x3f_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_482_; 
v_document_432_ = lean_ctor_get(v_z_430_, 0);
v_spine_433_ = lean_ctor_get(v_z_430_, 1);
v_openLeaf_x3f_434_ = lean_ctor_get(v_z_430_, 2);
v_blankLineFloor_x3f_435_ = lean_ctor_get(v_z_430_, 3);
v_isSharedCheck_482_ = !lean_is_exclusive(v_z_430_);
if (v_isSharedCheck_482_ == 0)
{
v___x_437_ = v_z_430_;
v_isShared_438_ = v_isSharedCheck_482_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_blankLineFloor_x3f_435_);
lean_inc(v_openLeaf_x3f_434_);
lean_inc(v_spine_433_);
lean_inc(v_document_432_);
lean_dec(v_z_430_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_482_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_array_get_size(v_spine_433_);
v___x_441_ = lean_nat_dec_lt(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v_fst_443_; lean_object* v_snd_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_454_; 
v___x_442_ = lean_apply_1(v_f_431_, v_document_432_);
v_fst_443_ = lean_ctor_get(v___x_442_, 0);
v_snd_444_ = lean_ctor_get(v___x_442_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_454_ == 0)
{
v___x_446_ = v___x_442_;
v_isShared_447_ = v_isSharedCheck_454_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_snd_444_);
lean_inc(v_fst_443_);
lean_dec(v___x_442_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_454_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v_fst_443_);
v___x_449_ = v___x_437_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_fst_443_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_spine_433_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_openLeaf_x3f_434_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_blankLineFloor_x3f_435_);
v___x_449_ = v_reuseFailAlloc_453_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_449_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_snd_444_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_frame_457_; lean_object* v_container_458_; lean_object* v_children_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_481_; 
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_sub(v___x_440_, v___x_455_);
v_frame_457_ = lean_array_fget(v_spine_433_, v___x_456_);
lean_dec(v___x_456_);
v_container_458_ = lean_ctor_get(v_frame_457_, 0);
v_children_459_ = lean_ctor_get(v_frame_457_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_frame_457_);
if (v_isSharedCheck_481_ == 0)
{
v___x_461_ = v_frame_457_;
v_isShared_462_ = v_isSharedCheck_481_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_children_459_);
lean_inc(v_container_458_);
lean_dec(v_frame_457_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_481_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v_fst_464_; lean_object* v_snd_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_480_; 
v___x_463_ = lean_apply_1(v_f_431_, v_children_459_);
v_fst_464_ = lean_ctor_get(v___x_463_, 0);
v_snd_465_ = lean_ctor_get(v___x_463_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_480_ == 0)
{
v___x_467_ = v___x_463_;
v_isShared_468_ = v_isSharedCheck_480_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_snd_465_);
lean_inc(v_fst_464_);
lean_dec(v___x_463_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_480_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_spine_469_; lean_object* v___x_471_; 
v_spine_469_ = lean_array_pop(v_spine_433_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v_fst_464_);
v___x_471_ = v___x_461_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_container_458_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_fst_464_);
v___x_471_ = v_reuseFailAlloc_479_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_array_push(v_spine_469_, v___x_471_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v___x_472_);
v___x_474_ = v___x_437_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_document_432_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_openLeaf_x3f_434_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_blankLineFloor_x3f_435_);
v___x_474_ = v_reuseFailAlloc_478_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_476_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_474_);
v___x_476_ = v___x_467_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_snd_465_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyGetChildren___boxed(lean_object* v_s_483_, lean_object* v_00_u03b1_484_, lean_object* v_z_485_, lean_object* v_f_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyGetChildren(v_s_483_, v_00_u03b1_484_, v_z_485_, v_f_486_);
lean_dec_ref(v_s_483_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushChild(lean_object* v_s_488_, lean_object* v_z_489_, lean_object* v_b_490_){
_start:
{
lean_object* v_document_491_; lean_object* v_spine_492_; lean_object* v_openLeaf_x3f_493_; lean_object* v_blankLineFloor_x3f_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_528_; 
v_document_491_ = lean_ctor_get(v_z_489_, 0);
v_spine_492_ = lean_ctor_get(v_z_489_, 1);
v_openLeaf_x3f_493_ = lean_ctor_get(v_z_489_, 2);
v_blankLineFloor_x3f_494_ = lean_ctor_get(v_z_489_, 3);
v_isSharedCheck_528_ = !lean_is_exclusive(v_z_489_);
if (v_isSharedCheck_528_ == 0)
{
v___x_496_ = v_z_489_;
v_isShared_497_ = v_isSharedCheck_528_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_blankLineFloor_x3f_494_);
lean_inc(v_openLeaf_x3f_493_);
lean_inc(v_spine_492_);
lean_inc(v_document_491_);
lean_dec(v_z_489_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_528_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_498_ = lean_array_get_size(v_spine_492_);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_nat_dec_eq(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_sub(v___x_498_, v___x_501_);
v___x_503_ = lean_nat_dec_lt(v___x_502_, v___x_498_);
if (v___x_503_ == 0)
{
lean_object* v___x_505_; 
lean_dec(v___x_502_);
lean_dec_ref(v_b_490_);
if (v_isShared_497_ == 0)
{
v___x_505_ = v___x_496_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_document_491_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_spine_492_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_openLeaf_x3f_493_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_blankLineFloor_x3f_494_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v_v_507_; lean_object* v_container_508_; lean_object* v_children_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_523_; 
v_v_507_ = lean_array_fget(v_spine_492_, v___x_502_);
v_container_508_ = lean_ctor_get(v_v_507_, 0);
v_children_509_ = lean_ctor_get(v_v_507_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_v_507_);
if (v_isSharedCheck_523_ == 0)
{
v___x_511_ = v_v_507_;
v_isShared_512_ = v_isSharedCheck_523_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_children_509_);
lean_inc(v_container_508_);
lean_dec(v_v_507_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_523_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v_xs_x27_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_513_ = lean_box(0);
v_xs_x27_514_ = lean_array_fset(v_spine_492_, v___x_502_, v___x_513_);
v___x_515_ = l_Lean_Markdown_Children_push(v_s_488_, v_children_509_, v_b_490_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v___x_515_);
v___x_517_ = v___x_511_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_container_508_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_515_);
v___x_517_ = v_reuseFailAlloc_522_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_array_fset(v_xs_x27_514_, v___x_502_, v___x_517_);
lean_dec(v___x_502_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_518_);
v___x_520_ = v___x_496_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_document_491_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_openLeaf_x3f_493_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_blankLineFloor_x3f_494_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = l_Lean_Markdown_Children_push(v_s_488_, v_document_491_, v_b_490_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_524_);
v___x_526_ = v___x_496_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_spine_492_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_openLeaf_x3f_493_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_blankLineFloor_x3f_494_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushChild___boxed(lean_object* v_s_529_, lean_object* v_z_530_, lean_object* v_b_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushChild(v_s_529_, v_z_530_, v_b_531_);
lean_dec_ref(v_s_529_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeLeaf(lean_object* v_s_533_, lean_object* v_z_534_){
_start:
{
lean_object* v_openLeaf_x3f_535_; 
v_openLeaf_x3f_535_ = lean_ctor_get(v_z_534_, 2);
if (lean_obj_tag(v_openLeaf_x3f_535_) == 0)
{
return v_z_534_;
}
else
{
lean_object* v_val_536_; lean_object* v___x_537_; lean_object* v_z_538_; lean_object* v_document_539_; lean_object* v_spine_540_; lean_object* v_blankLineFloor_x3f_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_549_; 
v_val_536_ = lean_ctor_get(v_openLeaf_x3f_535_, 0);
lean_inc(v_val_536_);
v___x_537_ = l_Lean_Markdown_BlockZipper_leafToBlock(v_s_533_, v_val_536_);
v_z_538_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushChild(v_s_533_, v_z_534_, v___x_537_);
v_document_539_ = lean_ctor_get(v_z_538_, 0);
v_spine_540_ = lean_ctor_get(v_z_538_, 1);
v_blankLineFloor_x3f_541_ = lean_ctor_get(v_z_538_, 3);
v_isSharedCheck_549_ = !lean_is_exclusive(v_z_538_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v_z_538_, 2);
lean_dec(v_unused_550_);
v___x_543_ = v_z_538_;
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_blankLineFloor_x3f_541_);
lean_inc(v_spine_540_);
lean_inc(v_document_539_);
lean_dec(v_z_538_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 2, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_document_539_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_spine_540_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_blankLineFloor_x3f_541_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeLeaf___boxed(lean_object* v_s_551_, lean_object* v_z_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_551_, v_z_552_);
lean_dec_ref(v_s_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg___lam__0(lean_object* v___x_554_, lean_object* v___x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_554_);
lean_ctor_set(v___x_557_, 1, v___x_555_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg___lam__0___boxed(lean_object* v___x_559_, lean_object* v___x_560_, lean_object* v_x_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg___lam__0(v___x_559_, v___x_560_, v_x_561_);
lean_dec(v_x_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg(lean_object* v___x_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___y_566_; lean_object* v_snd_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_610_; 
v_snd_570_ = lean_ctor_get(v_a_564_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_a_564_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v_a_564_, 0);
lean_dec(v_unused_611_);
v___x_572_ = v_a_564_;
v_isShared_573_ = v_isSharedCheck_610_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_snd_570_);
lean_dec(v_a_564_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_610_;
goto v_resetjp_571_;
}
v___jp_565_:
{
if (lean_obj_tag(v___y_566_) == 0)
{
lean_object* v_a_567_; 
v_a_567_ = lean_ctor_get(v___y_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___y_566_, 1);
return v_a_567_;
}
else
{
lean_object* v_a_568_; 
v_a_568_ = lean_ctor_get(v___y_566_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___y_566_, 1);
v_a_564_ = v_a_568_;
goto _start;
}
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = lean_box(0);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_nat_dec_lt(v___x_575_, v_snd_570_);
if (v___x_576_ == 0)
{
lean_object* v___x_578_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_574_);
v___x_578_ = v___x_572_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_570_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_sub(v_snd_570_, v___x_580_);
lean_dec(v_snd_570_);
v___x_582_ = lean_array_get_size(v___x_563_);
v___x_583_ = lean_nat_dec_lt(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
lean_del_object(v___x_572_);
v___x_584_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg___lam__0(v___x_574_, v___x_581_, v___x_574_);
v___y_566_ = v___x_584_;
goto v___jp_565_;
}
else
{
lean_object* v___x_585_; lean_object* v_container_586_; 
v___x_585_ = lean_array_fget(v___x_563_, v___x_581_);
v_container_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_container_586_);
if (lean_obj_tag(v_container_586_) == 0)
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_597_; 
lean_dec(v___x_585_);
v_isSharedCheck_597_ = !lean_is_exclusive(v_container_586_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v_container_586_, 0);
lean_dec(v_unused_598_);
v___x_588_ = v_container_586_;
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
else
{
lean_dec(v_container_586_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_597_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = lean_nat_add(v___x_581_, v___x_580_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 1);
lean_ctor_set(v___x_588_, 0, v___x_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_596_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v___x_581_);
lean_ctor_set(v___x_572_, 0, v___x_592_);
v___x_594_ = v___x_572_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_581_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_children_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_608_; 
lean_del_object(v___x_572_);
v_children_599_ = lean_ctor_get(v___x_585_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_585_, 0);
lean_dec(v_unused_609_);
v___x_601_ = v___x_585_;
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_children_599_);
lean_dec(v___x_585_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_608_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_container_586_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_children_599_);
v___x_604_ = v_reuseFailAlloc_607_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___x_606_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg___lam__0(v___x_574_, v___x_581_, v___x_605_);
lean_dec_ref_known(v___x_605_, 1);
v___y_566_ = v___x_606_;
goto v___jp_565_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg___boxed(lean_object* v___x_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg(v___x_612_, v_a_613_);
lean_dec_ref(v___x_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_listLikeFloor(lean_object* v_s_615_, lean_object* v_z_616_){
_start:
{
lean_object* v_spine_617_; lean_object* v_i_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_fst_622_; 
v_spine_617_ = lean_ctor_get(v_z_616_, 1);
v_i_618_ = lean_array_get_size(v_spine_617_);
v___x_619_ = lean_box(0);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v_i_618_);
v___x_621_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg(v_spine_617_, v___x_620_);
v_fst_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_fst_622_);
lean_dec_ref(v___x_621_);
if (lean_obj_tag(v_fst_622_) == 0)
{
lean_object* v___x_623_; 
v___x_623_ = lean_unsigned_to_nat(0u);
return v___x_623_;
}
else
{
lean_object* v_val_624_; 
v_val_624_ = lean_ctor_get(v_fst_622_, 0);
lean_inc(v_val_624_);
lean_dec_ref_known(v_fst_622_, 1);
return v_val_624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_listLikeFloor___boxed(lean_object* v_s_625_, lean_object* v_z_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Markdown_BlockZipper_listLikeFloor(v_s_625_, v_z_626_);
lean_dec_ref(v_z_626_);
lean_dec_ref(v_s_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0(lean_object* v___x_628_, lean_object* v_s_629_, lean_object* v_inst_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___redArg(v___x_628_, v_a_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0___boxed(lean_object* v___x_633_, lean_object* v_s_634_, lean_object* v_inst_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_listLikeFloor_spec__0(v___x_633_, v_s_634_, v_inst_635_, v_a_636_);
lean_dec_ref(v_s_634_);
lean_dec_ref(v___x_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_recordBlankLine(lean_object* v_s_638_, lean_object* v_z_639_){
_start:
{
lean_object* v_document_640_; lean_object* v_spine_641_; lean_object* v_openLeaf_x3f_642_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_document_640_ = lean_ctor_get(v_z_639_, 0);
lean_inc_ref(v_document_640_);
v_spine_641_ = lean_ctor_get(v_z_639_, 1);
lean_inc_ref(v_spine_641_);
v_openLeaf_x3f_642_ = lean_ctor_get(v_z_639_, 2);
lean_inc(v_openLeaf_x3f_642_);
v___x_660_ = lean_array_get_size(v_spine_641_);
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = lean_nat_sub(v___x_660_, v___x_661_);
v___x_663_ = lean_nat_dec_lt(v___x_662_, v___x_660_);
if (v___x_663_ == 0)
{
lean_object* v_pendingList_x3f_664_; 
lean_dec(v___x_662_);
v_pendingList_x3f_664_ = lean_ctor_get(v_document_640_, 1);
if (lean_obj_tag(v_pendingList_x3f_664_) == 0)
{
lean_dec_ref(v_z_639_);
goto v___jp_657_;
}
else
{
goto v___jp_643_;
}
}
else
{
lean_object* v___x_665_; lean_object* v_container_666_; 
v___x_665_ = lean_array_fget_borrowed(v_spine_641_, v___x_662_);
lean_dec(v___x_662_);
v_container_666_ = lean_ctor_get(v___x_665_, 0);
if (lean_obj_tag(v_container_666_) == 1)
{
goto v___jp_643_;
}
else
{
lean_object* v_children_667_; lean_object* v_pendingList_x3f_668_; 
v_children_667_ = lean_ctor_get(v___x_665_, 1);
v_pendingList_x3f_668_ = lean_ctor_get(v_children_667_, 1);
if (lean_obj_tag(v_pendingList_x3f_668_) == 0)
{
lean_dec_ref(v_z_639_);
goto v___jp_657_;
}
else
{
goto v___jp_643_;
}
}
}
v___jp_643_:
{
lean_object* v___x_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_652_; 
v___x_644_ = l_Lean_Markdown_BlockZipper_listLikeFloor(v_s_638_, v_z_639_);
v_isSharedCheck_652_ = !lean_is_exclusive(v_z_639_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; lean_object* v_unused_654_; lean_object* v_unused_655_; lean_object* v_unused_656_; 
v_unused_653_ = lean_ctor_get(v_z_639_, 3);
lean_dec(v_unused_653_);
v_unused_654_ = lean_ctor_get(v_z_639_, 2);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v_z_639_, 1);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_z_639_, 0);
lean_dec(v_unused_656_);
v___x_646_ = v_z_639_;
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
else
{
lean_dec(v_z_639_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 3, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_document_640_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_spine_641_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_openLeaf_x3f_642_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
v___jp_657_:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_box(0);
v___x_659_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_659_, 0, v_document_640_);
lean_ctor_set(v___x_659_, 1, v_spine_641_);
lean_ctor_set(v___x_659_, 2, v_openLeaf_x3f_642_);
lean_ctor_set(v___x_659_, 3, v___x_658_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_recordBlankLine___boxed(lean_object* v_s_669_, lean_object* v_z_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Markdown_BlockZipper_recordBlankLine(v_s_669_, v_z_670_);
lean_dec_ref(v_s_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_recordContentLine___redArg(lean_object* v_z_672_){
_start:
{
lean_object* v_document_673_; lean_object* v_spine_674_; lean_object* v_openLeaf_x3f_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_683_; 
v_document_673_ = lean_ctor_get(v_z_672_, 0);
v_spine_674_ = lean_ctor_get(v_z_672_, 1);
v_openLeaf_x3f_675_ = lean_ctor_get(v_z_672_, 2);
v_isSharedCheck_683_ = !lean_is_exclusive(v_z_672_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v_z_672_, 3);
lean_dec(v_unused_684_);
v___x_677_ = v_z_672_;
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_openLeaf_x3f_675_);
lean_inc(v_spine_674_);
lean_inc(v_document_673_);
lean_dec(v_z_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = lean_box(0);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 3, v___x_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_document_673_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_spine_674_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_openLeaf_x3f_675_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_recordContentLine(lean_object* v_s_685_, lean_object* v_z_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v_z_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_recordContentLine___boxed(lean_object* v_s_688_, lean_object* v_z_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Markdown_BlockZipper_recordContentLine(v_s_688_, v_z_689_);
lean_dec_ref(v_s_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove___redArg(lean_object* v_z_691_, lean_object* v_floor_692_){
_start:
{
lean_object* v_document_693_; lean_object* v_spine_694_; lean_object* v_openLeaf_x3f_695_; lean_object* v_blankLineFloor_x3f_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_document_693_ = lean_ctor_get(v_z_691_, 0);
v_spine_694_ = lean_ctor_get(v_z_691_, 1);
v_openLeaf_x3f_695_ = lean_ctor_get(v_z_691_, 2);
v_blankLineFloor_x3f_696_ = lean_ctor_get(v_z_691_, 3);
v___x_697_ = lean_array_get_size(v_spine_694_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_dec_eq(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v_top_701_; uint8_t v___x_702_; 
v___x_700_ = lean_unsigned_to_nat(1u);
v_top_701_ = lean_nat_sub(v___x_697_, v___x_700_);
v___x_702_ = lean_nat_dec_lt(v_top_701_, v_floor_692_);
if (v___x_702_ == 0)
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_750_; 
lean_inc(v_blankLineFloor_x3f_696_);
lean_inc(v_openLeaf_x3f_695_);
lean_inc_ref(v_spine_694_);
lean_inc_ref(v_document_693_);
v_isSharedCheck_750_ = !lean_is_exclusive(v_z_691_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_751_ = lean_ctor_get(v_z_691_, 3);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_z_691_, 2);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_z_691_, 1);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_z_691_, 0);
lean_dec(v_unused_754_);
v___x_704_ = v_z_691_;
v_isShared_705_ = v_isSharedCheck_750_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_z_691_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_750_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint8_t v___x_706_; 
v___x_706_ = lean_nat_dec_lt(v_top_701_, v___x_697_);
if (v___x_706_ == 0)
{
lean_object* v___x_708_; 
lean_dec(v_top_701_);
if (v_isShared_705_ == 0)
{
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_document_693_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_spine_694_);
lean_ctor_set(v_reuseFailAlloc_709_, 2, v_openLeaf_x3f_695_);
lean_ctor_set(v_reuseFailAlloc_709_, 3, v_blankLineFloor_x3f_696_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
lean_object* v_v_710_; lean_object* v_container_711_; lean_object* v_children_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_749_; 
v_v_710_ = lean_array_fget(v_spine_694_, v_top_701_);
v_container_711_ = lean_ctor_get(v_v_710_, 0);
v_children_712_ = lean_ctor_get(v_v_710_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_v_710_);
if (v_isSharedCheck_749_ == 0)
{
v___x_714_ = v_v_710_;
v_isShared_715_ = v_isSharedCheck_749_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_children_712_);
lean_inc(v_container_711_);
lean_dec(v_v_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_749_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v_xs_x27_717_; lean_object* v___y_719_; 
v___x_716_ = lean_box(0);
v_xs_x27_717_ = lean_array_fset(v_spine_694_, v_top_701_, v___x_716_);
if (lean_obj_tag(v_container_711_) == 1)
{
lean_object* v_list_724_; lean_object* v_marker_725_; lean_object* v_contentColumn_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_745_; 
v_list_724_ = lean_ctor_get(v_container_711_, 0);
v_marker_725_ = lean_ctor_get(v_container_711_, 1);
v_contentColumn_726_ = lean_ctor_get(v_container_711_, 2);
v_isSharedCheck_745_ = !lean_is_exclusive(v_container_711_);
if (v_isSharedCheck_745_ == 0)
{
v___x_728_ = v_container_711_;
v_isShared_729_ = v_isSharedCheck_745_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_contentColumn_726_);
lean_inc(v_marker_725_);
lean_inc(v_list_724_);
lean_dec(v_container_711_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_745_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_kind_730_; lean_object* v_items_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_744_; 
v_kind_730_ = lean_ctor_get(v_list_724_, 0);
v_items_731_ = lean_ctor_get(v_list_724_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_list_724_);
if (v_isSharedCheck_744_ == 0)
{
v___x_733_ = v_list_724_;
v_isShared_734_ = v_isSharedCheck_744_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_items_731_);
lean_inc(v_kind_730_);
lean_dec(v_list_724_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_744_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_kind_730_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_items_731_);
v___x_736_ = v_reuseFailAlloc_743_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_738_; 
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*2, v___x_706_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_736_);
v___x_738_ = v___x_728_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_marker_725_);
lean_ctor_set(v_reuseFailAlloc_742_, 2, v_contentColumn_726_);
v___x_738_ = v_reuseFailAlloc_742_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_740_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_738_);
v___x_740_ = v___x_714_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_children_712_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
v___y_719_ = v___x_740_;
goto v___jp_718_;
}
}
}
}
}
}
else
{
lean_object* v___x_747_; 
if (v_isShared_715_ == 0)
{
v___x_747_ = v___x_714_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_container_711_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_children_712_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
v___y_719_ = v___x_747_;
goto v___jp_718_;
}
}
v___jp_718_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_array_fset(v_xs_x27_717_, v_top_701_, v___y_719_);
lean_dec(v_top_701_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v___x_720_);
v___x_722_ = v___x_704_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_document_693_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_openLeaf_x3f_695_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_blankLineFloor_x3f_696_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
else
{
lean_dec(v_top_701_);
return v_z_691_;
}
}
else
{
return v_z_691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove___redArg___boxed(lean_object* v_z_755_, lean_object* v_floor_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove___redArg(v_z_755_, v_floor_756_);
lean_dec(v_floor_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove(lean_object* v_s_758_, lean_object* v_z_759_, lean_object* v_floor_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove___redArg(v_z_759_, v_floor_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove___boxed(lean_object* v_s_762_, lean_object* v_z_763_, lean_object* v_floor_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove(v_s_762_, v_z_763_, v_floor_764_);
lean_dec(v_floor_764_);
lean_dec_ref(v_s_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock___redArg(lean_object* v_z_766_){
_start:
{
lean_object* v_blankLineFloor_x3f_767_; 
v_blankLineFloor_x3f_767_ = lean_ctor_get(v_z_766_, 3);
if (lean_obj_tag(v_blankLineFloor_x3f_767_) == 0)
{
return v_z_766_;
}
else
{
lean_object* v_val_768_; lean_object* v___x_769_; lean_object* v_document_770_; lean_object* v_spine_771_; lean_object* v_openLeaf_x3f_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_780_; 
v_val_768_ = lean_ctor_get(v_blankLineFloor_x3f_767_, 0);
lean_inc(v_val_768_);
v___x_769_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_markLooseAbove___redArg(v_z_766_, v_val_768_);
lean_dec(v_val_768_);
v_document_770_ = lean_ctor_get(v___x_769_, 0);
v_spine_771_ = lean_ctor_get(v___x_769_, 1);
v_openLeaf_x3f_772_ = lean_ctor_get(v___x_769_, 2);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v___x_769_, 3);
lean_dec(v_unused_781_);
v___x_774_ = v___x_769_;
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_openLeaf_x3f_772_);
lean_inc(v_spine_771_);
lean_inc(v_document_770_);
lean_dec(v___x_769_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_box(0);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 3, v___x_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_document_770_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_spine_771_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_openLeaf_x3f_772_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock(lean_object* v_s_782_, lean_object* v_z_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock___redArg(v_z_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock___boxed(lean_object* v_s_785_, lean_object* v_z_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock(v_s_785_, v_z_786_);
lean_dec_ref(v_s_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeContainer(lean_object* v_s_788_, lean_object* v_z_789_){
_start:
{
lean_object* v_z_790_; lean_object* v_document_791_; lean_object* v_spine_792_; lean_object* v_openLeaf_x3f_793_; lean_object* v_blankLineFloor_x3f_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_z_790_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_788_, v_z_789_);
v_document_791_ = lean_ctor_get(v_z_790_, 0);
v_spine_792_ = lean_ctor_get(v_z_790_, 1);
v_openLeaf_x3f_793_ = lean_ctor_get(v_z_790_, 2);
v_blankLineFloor_x3f_794_ = lean_ctor_get(v_z_790_, 3);
v___x_795_ = lean_unsigned_to_nat(0u);
v___x_796_ = lean_array_get_size(v_spine_792_);
v___x_797_ = lean_nat_dec_lt(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
return v_z_790_;
}
else
{
lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_872_; 
lean_inc(v_blankLineFloor_x3f_794_);
lean_inc(v_openLeaf_x3f_793_);
lean_inc_ref(v_spine_792_);
lean_inc_ref(v_document_791_);
v_isSharedCheck_872_ = !lean_is_exclusive(v_z_790_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; lean_object* v_unused_874_; lean_object* v_unused_875_; lean_object* v_unused_876_; 
v_unused_873_ = lean_ctor_get(v_z_790_, 3);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_z_790_, 2);
lean_dec(v_unused_874_);
v_unused_875_ = lean_ctor_get(v_z_790_, 1);
lean_dec(v_unused_875_);
v_unused_876_ = lean_ctor_get(v_z_790_, 0);
lean_dec(v_unused_876_);
v___x_799_ = v_z_790_;
v_isShared_800_ = v_isSharedCheck_872_;
goto v_resetjp_798_;
}
else
{
lean_dec(v_z_790_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_872_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_frame_803_; lean_object* v_container_804_; lean_object* v_children_805_; lean_object* v___x_806_; lean_object* v_children_807_; 
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_sub(v___x_796_, v___x_801_);
v_frame_803_ = lean_array_fget_borrowed(v_spine_792_, v___x_802_);
lean_dec(v___x_802_);
v_container_804_ = lean_ctor_get(v_frame_803_, 0);
lean_inc_ref(v_container_804_);
v_children_805_ = lean_ctor_get(v_frame_803_, 1);
lean_inc_ref(v_children_805_);
v___x_806_ = lean_array_pop(v_spine_792_);
v_children_807_ = l_Lean_Markdown_Children_flushLists(v_s_788_, v_children_805_);
if (lean_obj_tag(v_container_804_) == 0)
{
lean_object* v_markers_808_; lean_object* v_blocks_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_820_; 
v_markers_808_ = lean_ctor_get(v_container_804_, 0);
lean_inc_ref(v_markers_808_);
lean_dec_ref_known(v_container_804_, 1);
v_blocks_809_ = lean_ctor_get(v_children_807_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v_children_807_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v_children_807_, 1);
lean_dec(v_unused_821_);
v___x_811_ = v_children_807_;
v_isShared_812_ = v_isSharedCheck_820_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_blocks_809_);
lean_dec(v_children_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_820_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_z_814_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_806_);
v_z_814_ = v___x_799_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_document_791_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_819_, 2, v_openLeaf_x3f_793_);
lean_ctor_set(v_reuseFailAlloc_819_, 3, v_blankLineFloor_x3f_794_);
v_z_814_ = v_reuseFailAlloc_819_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 6);
lean_ctor_set(v___x_811_, 1, v_blocks_809_);
lean_ctor_set(v___x_811_, 0, v_markers_808_);
v___x_816_ = v___x_811_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_markers_808_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_blocks_809_);
v___x_816_ = v_reuseFailAlloc_818_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; 
v___x_817_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushChild(v_s_788_, v_z_814_, v___x_816_);
return v___x_817_;
}
}
}
}
else
{
lean_object* v_list_822_; lean_object* v_marker_823_; lean_object* v_kind_824_; uint8_t v_loose_825_; lean_object* v_items_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_871_; 
v_list_822_ = lean_ctor_get(v_container_804_, 0);
lean_inc_ref(v_list_822_);
v_marker_823_ = lean_ctor_get(v_container_804_, 1);
lean_inc_ref(v_marker_823_);
lean_dec_ref_known(v_container_804_, 3);
v_kind_824_ = lean_ctor_get(v_list_822_, 0);
v_loose_825_ = lean_ctor_get_uint8(v_list_822_, sizeof(void*)*2);
v_items_826_ = lean_ctor_get(v_list_822_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_list_822_);
if (v_isSharedCheck_871_ == 0)
{
v___x_828_ = v_list_822_;
v_isShared_829_ = v_isSharedCheck_871_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_items_826_);
lean_inc(v_kind_824_);
lean_dec(v_list_822_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_871_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_blocks_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_869_; 
v_blocks_830_ = lean_ctor_get(v_children_807_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_children_807_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_children_807_, 1);
lean_dec(v_unused_870_);
v___x_832_ = v_children_807_;
v_isShared_833_ = v_isSharedCheck_869_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_blocks_830_);
lean_dec(v_children_807_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_869_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_blocks_830_);
lean_ctor_set(v___x_832_, 0, v_marker_823_);
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_marker_823_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_blocks_830_);
v___x_835_ = v_reuseFailAlloc_868_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; lean_object* v_list_838_; 
v___x_836_ = lean_array_push(v_items_826_, v___x_835_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_836_);
v_list_838_ = v___x_828_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_kind_824_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_836_);
lean_ctor_set_uint8(v_reuseFailAlloc_867_, sizeof(void*)*2, v_loose_825_);
v_list_838_ = v_reuseFailAlloc_867_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = lean_array_get_size(v___x_806_);
v___x_840_ = lean_nat_dec_eq(v___x_839_, v___x_795_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = lean_nat_sub(v___x_839_, v___x_801_);
v___x_842_ = lean_nat_dec_lt(v___x_841_, v___x_839_);
if (v___x_842_ == 0)
{
lean_object* v___x_844_; 
lean_dec(v___x_841_);
lean_dec_ref(v_list_838_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_806_);
v___x_844_ = v___x_799_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_document_791_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_openLeaf_x3f_793_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v_blankLineFloor_x3f_794_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
lean_object* v_v_846_; lean_object* v_container_847_; lean_object* v_children_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_862_; 
v_v_846_ = lean_array_fget(v___x_806_, v___x_841_);
v_container_847_ = lean_ctor_get(v_v_846_, 0);
v_children_848_ = lean_ctor_get(v_v_846_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_v_846_);
if (v_isSharedCheck_862_ == 0)
{
v___x_850_ = v_v_846_;
v_isShared_851_ = v_isSharedCheck_862_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_children_848_);
lean_inc(v_container_847_);
lean_dec(v_v_846_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_862_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v_xs_x27_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_852_ = lean_box(0);
v_xs_x27_853_ = lean_array_fset(v___x_806_, v___x_841_, v___x_852_);
v___x_854_ = l_Lean_Markdown_Children_setPendingList(v_s_788_, v_children_848_, v_list_838_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___x_854_);
v___x_856_ = v___x_850_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_container_847_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_861_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = lean_array_fset(v_xs_x27_853_, v___x_841_, v___x_856_);
lean_dec(v___x_841_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_857_);
v___x_859_ = v___x_799_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_document_791_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_openLeaf_x3f_793_);
lean_ctor_set(v_reuseFailAlloc_860_, 3, v_blankLineFloor_x3f_794_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = l_Lean_Markdown_Children_setPendingList(v_s_788_, v_document_791_, v_list_838_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_806_);
lean_ctor_set(v___x_799_, 0, v___x_863_);
v___x_865_ = v___x_799_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_openLeaf_x3f_793_);
lean_ctor_set(v_reuseFailAlloc_866_, 3, v_blankLineFloor_x3f_794_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
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
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeContainer___boxed(lean_object* v_s_877_, lean_object* v_z_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Markdown_BlockZipper_closeContainer(v_s_877_, v_z_878_);
lean_dec_ref(v_s_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openBlockquote(lean_object* v_s_880_, lean_object* v_z_881_, lean_object* v_markers_882_){
_start:
{
lean_object* v___x_883_; lean_object* v_z_884_; lean_object* v_document_885_; lean_object* v_spine_886_; lean_object* v_openLeaf_x3f_887_; lean_object* v_blankLineFloor_x3f_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_899_; 
v___x_883_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_880_, v_z_881_);
v_z_884_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock___redArg(v___x_883_);
v_document_885_ = lean_ctor_get(v_z_884_, 0);
v_spine_886_ = lean_ctor_get(v_z_884_, 1);
v_openLeaf_x3f_887_ = lean_ctor_get(v_z_884_, 2);
v_blankLineFloor_x3f_888_ = lean_ctor_get(v_z_884_, 3);
v_isSharedCheck_899_ = !lean_is_exclusive(v_z_884_);
if (v_isSharedCheck_899_ == 0)
{
v___x_890_ = v_z_884_;
v_isShared_891_ = v_isSharedCheck_899_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_blankLineFloor_x3f_888_);
lean_inc(v_openLeaf_x3f_887_);
lean_inc(v_spine_886_);
lean_inc(v_document_885_);
lean_dec(v_z_884_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_899_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v_markers_882_);
v___x_893_ = lean_obj_once(&l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0, &l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0_once, _init_l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_array_push(v_spine_886_, v___x_894_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v___x_895_);
v___x_897_ = v___x_890_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_document_885_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_898_, 2, v_openLeaf_x3f_887_);
lean_ctor_set(v_reuseFailAlloc_898_, 3, v_blankLineFloor_x3f_888_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openBlockquote___boxed(lean_object* v_s_900_, lean_object* v_z_901_, lean_object* v_markers_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Markdown_BlockZipper_openBlockquote(v_s_900_, v_z_901_, v_markers_902_);
lean_dec_ref(v_s_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openItem(lean_object* v_s_906_, lean_object* v_z_907_, lean_object* v_kind_908_, lean_object* v_marker_909_, lean_object* v_contentColumn_910_){
_start:
{
lean_object* v_fst_912_; lean_object* v_snd_913_; lean_object* v_z_950_; lean_object* v_document_951_; lean_object* v_spine_952_; lean_object* v_openLeaf_x3f_953_; lean_object* v_blankLineFloor_x3f_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_987_; 
v_z_950_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_906_, v_z_907_);
v_document_951_ = lean_ctor_get(v_z_950_, 0);
v_spine_952_ = lean_ctor_get(v_z_950_, 1);
v_openLeaf_x3f_953_ = lean_ctor_get(v_z_950_, 2);
v_blankLineFloor_x3f_954_ = lean_ctor_get(v_z_950_, 3);
v_isSharedCheck_987_ = !lean_is_exclusive(v_z_950_);
if (v_isSharedCheck_987_ == 0)
{
v___x_956_ = v_z_950_;
v_isShared_957_ = v_isSharedCheck_987_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_blankLineFloor_x3f_954_);
lean_inc(v_openLeaf_x3f_953_);
lean_inc(v_spine_952_);
lean_inc(v_document_951_);
lean_dec(v_z_950_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_987_;
goto v_resetjp_955_;
}
v___jp_911_:
{
if (lean_obj_tag(v_snd_913_) == 0)
{
lean_object* v_z_914_; lean_object* v_document_915_; lean_object* v_spine_916_; lean_object* v_openLeaf_x3f_917_; lean_object* v_blankLineFloor_x3f_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_932_; 
v_z_914_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock___redArg(v_fst_912_);
v_document_915_ = lean_ctor_get(v_z_914_, 0);
v_spine_916_ = lean_ctor_get(v_z_914_, 1);
v_openLeaf_x3f_917_ = lean_ctor_get(v_z_914_, 2);
v_blankLineFloor_x3f_918_ = lean_ctor_get(v_z_914_, 3);
v_isSharedCheck_932_ = !lean_is_exclusive(v_z_914_);
if (v_isSharedCheck_932_ == 0)
{
v___x_920_ = v_z_914_;
v_isShared_921_ = v_isSharedCheck_932_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_blankLineFloor_x3f_918_);
lean_inc(v_openLeaf_x3f_917_);
lean_inc(v_spine_916_);
lean_inc(v_document_915_);
lean_dec(v_z_914_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_932_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_922_ = 0;
v___x_923_ = ((lean_object*)(l_Lean_Markdown_BlockZipper_openItem___closed__0));
v___x_924_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_924_, 0, v_kind_908_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*2, v___x_922_);
v___x_925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v_marker_909_);
lean_ctor_set(v___x_925_, 2, v_contentColumn_910_);
v___x_926_ = lean_obj_once(&l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0, &l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0_once, _init_l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_array_push(v_spine_916_, v___x_927_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v___x_928_);
v___x_930_ = v___x_920_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_document_915_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_openLeaf_x3f_917_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_blankLineFloor_x3f_918_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_object* v_val_933_; lean_object* v_document_934_; lean_object* v_spine_935_; lean_object* v_openLeaf_x3f_936_; lean_object* v_blankLineFloor_x3f_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v_kind_908_);
v_val_933_ = lean_ctor_get(v_snd_913_, 0);
lean_inc(v_val_933_);
lean_dec_ref_known(v_snd_913_, 1);
v_document_934_ = lean_ctor_get(v_fst_912_, 0);
v_spine_935_ = lean_ctor_get(v_fst_912_, 1);
v_openLeaf_x3f_936_ = lean_ctor_get(v_fst_912_, 2);
v_blankLineFloor_x3f_937_ = lean_ctor_get(v_fst_912_, 3);
v_isSharedCheck_949_ = !lean_is_exclusive(v_fst_912_);
if (v_isSharedCheck_949_ == 0)
{
v___x_939_ = v_fst_912_;
v_isShared_940_ = v_isSharedCheck_949_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_blankLineFloor_x3f_937_);
lean_inc(v_openLeaf_x3f_936_);
lean_inc(v_spine_935_);
lean_inc(v_document_934_);
lean_dec(v_fst_912_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_949_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_z_946_; 
v___x_941_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_941_, 0, v_val_933_);
lean_ctor_set(v___x_941_, 1, v_marker_909_);
lean_ctor_set(v___x_941_, 2, v_contentColumn_910_);
v___x_942_ = lean_obj_once(&l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0, &l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0_once, _init_l_Lean_Markdown_instInhabitedZipperFrame_default___redArg___closed__0);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_array_push(v_spine_935_, v___x_943_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_944_);
v_z_946_ = v___x_939_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_document_934_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_openLeaf_x3f_936_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_blankLineFloor_x3f_937_);
v_z_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock___redArg(v_z_946_);
return v___x_947_;
}
}
}
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_array_get_size(v_spine_952_);
v___x_960_ = lean_nat_dec_lt(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v_fst_962_; lean_object* v_snd_963_; lean_object* v___x_965_; 
v___x_961_ = l_Lean_Markdown_Children_takePendingList___redArg(v_document_951_, v_kind_908_);
v_fst_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_fst_962_);
v_snd_963_ = lean_ctor_get(v___x_961_, 1);
lean_inc(v_snd_963_);
lean_dec_ref(v___x_961_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v_fst_962_);
v___x_965_ = v___x_956_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_fst_962_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_spine_952_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_openLeaf_x3f_953_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_blankLineFloor_x3f_954_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
v_fst_912_ = v___x_965_;
v_snd_913_ = v_snd_963_;
goto v___jp_911_;
}
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_frame_969_; lean_object* v_container_970_; lean_object* v_children_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_986_; 
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_sub(v___x_959_, v___x_967_);
v_frame_969_ = lean_array_fget(v_spine_952_, v___x_968_);
lean_dec(v___x_968_);
v_container_970_ = lean_ctor_get(v_frame_969_, 0);
v_children_971_ = lean_ctor_get(v_frame_969_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v_frame_969_);
if (v_isSharedCheck_986_ == 0)
{
v___x_973_ = v_frame_969_;
v_isShared_974_ = v_isSharedCheck_986_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_children_971_);
lean_inc(v_container_970_);
lean_dec(v_frame_969_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_986_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; lean_object* v_fst_976_; lean_object* v_snd_977_; lean_object* v_spine_978_; lean_object* v___x_980_; 
v___x_975_ = l_Lean_Markdown_Children_takePendingList___redArg(v_children_971_, v_kind_908_);
v_fst_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_fst_976_);
v_snd_977_ = lean_ctor_get(v___x_975_, 1);
lean_inc(v_snd_977_);
lean_dec_ref(v___x_975_);
v_spine_978_ = lean_array_pop(v_spine_952_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 1, v_fst_976_);
v___x_980_ = v___x_973_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_container_970_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_fst_976_);
v___x_980_ = v_reuseFailAlloc_985_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_array_push(v_spine_978_, v___x_980_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___x_981_);
v___x_983_ = v___x_956_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_document_951_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_openLeaf_x3f_953_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_blankLineFloor_x3f_954_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
v_fst_912_ = v___x_983_;
v_snd_913_ = v_snd_977_;
goto v___jp_911_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openItem___boxed(lean_object* v_s_988_, lean_object* v_z_989_, lean_object* v_kind_990_, lean_object* v_marker_991_, lean_object* v_contentColumn_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Markdown_BlockZipper_openItem(v_s_988_, v_z_989_, v_kind_990_, v_marker_991_, v_contentColumn_992_);
lean_dec_ref(v_s_988_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openLeaf(lean_object* v_s_994_, lean_object* v_z_995_, lean_object* v_l_996_){
_start:
{
lean_object* v___x_997_; lean_object* v_z_998_; lean_object* v_document_999_; lean_object* v_spine_1000_; lean_object* v_blankLineFloor_x3f_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1009_; 
v___x_997_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_994_, v_z_995_);
v_z_998_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock___redArg(v___x_997_);
v_document_999_ = lean_ctor_get(v_z_998_, 0);
v_spine_1000_ = lean_ctor_get(v_z_998_, 1);
v_blankLineFloor_x3f_1001_ = lean_ctor_get(v_z_998_, 3);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_z_998_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_z_998_, 2);
lean_dec(v_unused_1010_);
v___x_1003_ = v_z_998_;
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_blankLineFloor_x3f_1001_);
lean_inc(v_spine_1000_);
lean_inc(v_document_999_);
lean_dec(v_z_998_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_l_996_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 2, v___x_1005_);
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_document_999_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_spine_1000_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1008_, 3, v_blankLineFloor_x3f_1001_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_openLeaf___boxed(lean_object* v_s_1011_, lean_object* v_z_1012_, lean_object* v_l_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_1011_, v_z_1012_, v_l_1013_);
lean_dec_ref(v_s_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_addBlock(lean_object* v_s_1015_, lean_object* v_z_1016_, lean_object* v_b_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_1015_, v_z_1016_);
v___x_1019_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_startBlock___redArg(v___x_1018_);
v___x_1020_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushChild(v_s_1015_, v___x_1019_, v_b_1017_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_addBlock___boxed(lean_object* v_s_1021_, lean_object* v_z_1022_, lean_object* v_b_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_1021_, v_z_1022_, v_b_1023_);
lean_dec_ref(v_s_1021_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyLeaf___redArg(lean_object* v_z_1025_, lean_object* v_f_1026_){
_start:
{
lean_object* v_openLeaf_x3f_1027_; 
v_openLeaf_x3f_1027_ = lean_ctor_get(v_z_1025_, 2);
lean_inc(v_openLeaf_x3f_1027_);
if (lean_obj_tag(v_openLeaf_x3f_1027_) == 0)
{
lean_dec_ref(v_f_1026_);
return v_z_1025_;
}
else
{
lean_object* v_document_1028_; lean_object* v_spine_1029_; lean_object* v_blankLineFloor_x3f_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1046_; 
v_document_1028_ = lean_ctor_get(v_z_1025_, 0);
v_spine_1029_ = lean_ctor_get(v_z_1025_, 1);
v_blankLineFloor_x3f_1030_ = lean_ctor_get(v_z_1025_, 3);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_z_1025_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_z_1025_, 2);
lean_dec(v_unused_1047_);
v___x_1032_ = v_z_1025_;
v_isShared_1033_ = v_isSharedCheck_1046_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_blankLineFloor_x3f_1030_);
lean_inc(v_spine_1029_);
lean_inc(v_document_1028_);
lean_dec(v_z_1025_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1046_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v_val_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1045_; 
v_val_1034_ = lean_ctor_get(v_openLeaf_x3f_1027_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_openLeaf_x3f_1027_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1036_ = v_openLeaf_x3f_1027_;
v_isShared_1037_ = v_isSharedCheck_1045_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_val_1034_);
lean_dec(v_openLeaf_x3f_1027_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1045_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1038_ = lean_apply_1(v_f_1026_, v_val_1034_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1038_);
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 2, v___x_1040_);
v___x_1042_ = v___x_1032_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_document_1028_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_spine_1029_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_blankLineFloor_x3f_1030_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyLeaf(lean_object* v_s_1048_, lean_object* v_z_1049_, lean_object* v_f_1050_){
_start:
{
lean_object* v_openLeaf_x3f_1051_; 
v_openLeaf_x3f_1051_ = lean_ctor_get(v_z_1049_, 2);
lean_inc(v_openLeaf_x3f_1051_);
if (lean_obj_tag(v_openLeaf_x3f_1051_) == 0)
{
lean_dec_ref(v_f_1050_);
return v_z_1049_;
}
else
{
lean_object* v_document_1052_; lean_object* v_spine_1053_; lean_object* v_blankLineFloor_x3f_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1070_; 
v_document_1052_ = lean_ctor_get(v_z_1049_, 0);
v_spine_1053_ = lean_ctor_get(v_z_1049_, 1);
v_blankLineFloor_x3f_1054_ = lean_ctor_get(v_z_1049_, 3);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_z_1049_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v_z_1049_, 2);
lean_dec(v_unused_1071_);
v___x_1056_ = v_z_1049_;
v_isShared_1057_ = v_isSharedCheck_1070_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_blankLineFloor_x3f_1054_);
lean_inc(v_spine_1053_);
lean_inc(v_document_1052_);
lean_dec(v_z_1049_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1070_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_val_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1069_; 
v_val_1058_ = lean_ctor_get(v_openLeaf_x3f_1051_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_openLeaf_x3f_1051_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1060_ = v_openLeaf_x3f_1051_;
v_isShared_1061_ = v_isSharedCheck_1069_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_val_1058_);
lean_dec(v_openLeaf_x3f_1051_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1069_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1062_ = lean_apply_1(v_f_1050_, v_val_1058_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 2, v___x_1064_);
v___x_1066_ = v___x_1056_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_document_1052_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_spine_1053_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_blankLineFloor_x3f_1054_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyLeaf___boxed(lean_object* v_s_1072_, lean_object* v_z_1073_, lean_object* v_f_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_modifyLeaf(v_s_1072_, v_z_1073_, v_f_1074_);
lean_dec_ref(v_s_1072_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendParagraph___redArg(lean_object* v_z_1076_, lean_object* v_line_1077_){
_start:
{
lean_object* v_document_1078_; lean_object* v_spine_1079_; lean_object* v_openLeaf_x3f_1080_; lean_object* v_blankLineFloor_x3f_1081_; lean_object* v___y_1083_; 
v_document_1078_ = lean_ctor_get(v_z_1076_, 0);
v_spine_1079_ = lean_ctor_get(v_z_1076_, 1);
v_openLeaf_x3f_1080_ = lean_ctor_get(v_z_1076_, 2);
v_blankLineFloor_x3f_1081_ = lean_ctor_get(v_z_1076_, 3);
if (lean_obj_tag(v_openLeaf_x3f_1080_) == 0)
{
lean_dec_ref(v_line_1077_);
return v_z_1076_;
}
else
{
lean_object* v_val_1086_; 
lean_inc_ref(v_openLeaf_x3f_1080_);
lean_inc(v_blankLineFloor_x3f_1081_);
lean_inc_ref(v_spine_1079_);
lean_inc_ref(v_document_1078_);
lean_dec_ref(v_z_1076_);
v_val_1086_ = lean_ctor_get(v_openLeaf_x3f_1080_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v_openLeaf_x3f_1080_, 1);
if (lean_obj_tag(v_val_1086_) == 0)
{
lean_object* v_lines_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1095_; 
v_lines_1087_ = lean_ctor_get(v_val_1086_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_val_1086_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1089_ = v_val_1086_;
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_lines_1087_);
lean_dec(v_val_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_array_push(v_lines_1087_, v_line_1077_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1091_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v___y_1083_ = v___x_1093_;
goto v___jp_1082_;
}
}
}
else
{
lean_dec_ref(v_line_1077_);
v___y_1083_ = v_val_1086_;
goto v___jp_1082_;
}
}
v___jp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___y_1083_);
v___x_1085_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1085_, 0, v_document_1078_);
lean_ctor_set(v___x_1085_, 1, v_spine_1079_);
lean_ctor_set(v___x_1085_, 2, v___x_1084_);
lean_ctor_set(v___x_1085_, 3, v_blankLineFloor_x3f_1081_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendParagraph(lean_object* v_s_1096_, lean_object* v_z_1097_, lean_object* v_line_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Markdown_BlockZipper_extendParagraph___redArg(v_z_1097_, v_line_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendParagraph___boxed(lean_object* v_s_1100_, lean_object* v_z_1101_, lean_object* v_line_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Markdown_BlockZipper_extendParagraph(v_s_1100_, v_z_1101_, v_line_1102_);
lean_dec_ref(v_s_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendFencedCode___redArg(lean_object* v_z_1104_, lean_object* v_line_1105_){
_start:
{
lean_object* v_document_1106_; lean_object* v_spine_1107_; lean_object* v_openLeaf_x3f_1108_; lean_object* v_blankLineFloor_x3f_1109_; lean_object* v___y_1111_; 
v_document_1106_ = lean_ctor_get(v_z_1104_, 0);
v_spine_1107_ = lean_ctor_get(v_z_1104_, 1);
v_openLeaf_x3f_1108_ = lean_ctor_get(v_z_1104_, 2);
v_blankLineFloor_x3f_1109_ = lean_ctor_get(v_z_1104_, 3);
if (lean_obj_tag(v_openLeaf_x3f_1108_) == 0)
{
lean_dec_ref(v_line_1105_);
return v_z_1104_;
}
else
{
lean_object* v_val_1114_; 
lean_inc_ref(v_openLeaf_x3f_1108_);
lean_inc(v_blankLineFloor_x3f_1109_);
lean_inc_ref(v_spine_1107_);
lean_inc_ref(v_document_1106_);
lean_dec_ref(v_z_1104_);
v_val_1114_ = lean_ctor_get(v_openLeaf_x3f_1108_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v_openLeaf_x3f_1108_, 1);
if (lean_obj_tag(v_val_1114_) == 1)
{
lean_object* v_info_1115_; lean_object* v_openFence_1116_; lean_object* v_lines_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1125_; 
v_info_1115_ = lean_ctor_get(v_val_1114_, 0);
v_openFence_1116_ = lean_ctor_get(v_val_1114_, 1);
v_lines_1117_ = lean_ctor_get(v_val_1114_, 2);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_val_1114_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1119_ = v_val_1114_;
v_isShared_1120_ = v_isSharedCheck_1125_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_lines_1117_);
lean_inc(v_openFence_1116_);
lean_inc(v_info_1115_);
lean_dec(v_val_1114_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1125_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1121_ = lean_array_push(v_lines_1117_, v_line_1105_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 2, v___x_1121_);
v___x_1123_ = v___x_1119_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_info_1115_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_openFence_1116_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
v___y_1111_ = v___x_1123_;
goto v___jp_1110_;
}
}
}
else
{
lean_dec_ref(v_line_1105_);
v___y_1111_ = v_val_1114_;
goto v___jp_1110_;
}
}
v___jp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1111_);
v___x_1113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1113_, 0, v_document_1106_);
lean_ctor_set(v___x_1113_, 1, v_spine_1107_);
lean_ctor_set(v___x_1113_, 2, v___x_1112_);
lean_ctor_set(v___x_1113_, 3, v_blankLineFloor_x3f_1109_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendFencedCode(lean_object* v_s_1126_, lean_object* v_z_1127_, lean_object* v_line_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_Markdown_BlockZipper_extendFencedCode___redArg(v_z_1127_, v_line_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendFencedCode___boxed(lean_object* v_s_1130_, lean_object* v_z_1131_, lean_object* v_line_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Markdown_BlockZipper_extendFencedCode(v_s_1130_, v_z_1131_, v_line_1132_);
lean_dec_ref(v_s_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendHtml___redArg(lean_object* v_z_1134_, lean_object* v_line_1135_){
_start:
{
lean_object* v_document_1136_; lean_object* v_spine_1137_; lean_object* v_openLeaf_x3f_1138_; lean_object* v_blankLineFloor_x3f_1139_; lean_object* v___y_1141_; 
v_document_1136_ = lean_ctor_get(v_z_1134_, 0);
v_spine_1137_ = lean_ctor_get(v_z_1134_, 1);
v_openLeaf_x3f_1138_ = lean_ctor_get(v_z_1134_, 2);
v_blankLineFloor_x3f_1139_ = lean_ctor_get(v_z_1134_, 3);
if (lean_obj_tag(v_openLeaf_x3f_1138_) == 0)
{
lean_dec_ref(v_line_1135_);
return v_z_1134_;
}
else
{
lean_object* v_val_1144_; 
lean_inc_ref(v_openLeaf_x3f_1138_);
lean_inc(v_blankLineFloor_x3f_1139_);
lean_inc_ref(v_spine_1137_);
lean_inc_ref(v_document_1136_);
lean_dec_ref(v_z_1134_);
v_val_1144_ = lean_ctor_get(v_openLeaf_x3f_1138_, 0);
lean_inc(v_val_1144_);
lean_dec_ref_known(v_openLeaf_x3f_1138_, 1);
if (lean_obj_tag(v_val_1144_) == 3)
{
uint8_t v_kind_1145_; lean_object* v_lines_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1154_; 
v_kind_1145_ = lean_ctor_get_uint8(v_val_1144_, sizeof(void*)*1);
v_lines_1146_ = lean_ctor_get(v_val_1144_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_val_1144_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1148_ = v_val_1144_;
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_lines_1146_);
lean_dec(v_val_1144_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = lean_array_push(v_lines_1146_, v_line_1135_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1150_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, sizeof(void*)*1, v_kind_1145_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
v___y_1141_ = v___x_1152_;
goto v___jp_1140_;
}
}
}
else
{
lean_dec_ref(v_line_1135_);
v___y_1141_ = v_val_1144_;
goto v___jp_1140_;
}
}
v___jp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___y_1141_);
v___x_1143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1143_, 0, v_document_1136_);
lean_ctor_set(v___x_1143_, 1, v_spine_1137_);
lean_ctor_set(v___x_1143_, 2, v___x_1142_);
lean_ctor_set(v___x_1143_, 3, v_blankLineFloor_x3f_1139_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendHtml(lean_object* v_s_1155_, lean_object* v_z_1156_, lean_object* v_line_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Lean_Markdown_BlockZipper_extendHtml___redArg(v_z_1156_, v_line_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_extendHtml___boxed(lean_object* v_s_1159_, lean_object* v_z_1160_, lean_object* v_line_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Markdown_BlockZipper_extendHtml(v_s_1159_, v_z_1160_, v_line_1161_);
lean_dec_ref(v_s_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeFencedCode(lean_object* v_s_1163_, lean_object* v_z_1164_, lean_object* v_closeFence_1165_){
_start:
{
lean_object* v_openLeaf_x3f_1166_; 
v_openLeaf_x3f_1166_ = lean_ctor_get(v_z_1164_, 2);
lean_inc(v_openLeaf_x3f_1166_);
if (lean_obj_tag(v_openLeaf_x3f_1166_) == 1)
{
lean_object* v_val_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1191_; 
v_val_1167_ = lean_ctor_get(v_openLeaf_x3f_1166_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_openLeaf_x3f_1166_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1169_ = v_openLeaf_x3f_1166_;
v_isShared_1170_ = v_isSharedCheck_1191_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_val_1167_);
lean_dec(v_openLeaf_x3f_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1191_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
if (lean_obj_tag(v_val_1167_) == 1)
{
lean_object* v_info_1171_; lean_object* v_openFence_1172_; lean_object* v_lines_1173_; lean_object* v___x_1175_; 
v_info_1171_ = lean_ctor_get(v_val_1167_, 0);
lean_inc_ref(v_info_1171_);
v_openFence_1172_ = lean_ctor_get(v_val_1167_, 1);
lean_inc_ref(v_openFence_1172_);
v_lines_1173_ = lean_ctor_get(v_val_1167_, 2);
lean_inc_ref(v_lines_1173_);
lean_dec_ref_known(v_val_1167_, 3);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v_closeFence_1165_);
v___x_1175_ = v___x_1169_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_closeFence_1165_);
v___x_1175_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v_z_1177_; lean_object* v_document_1178_; lean_object* v_spine_1179_; lean_object* v_blankLineFloor_x3f_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1188_; 
v___x_1176_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1176_, 0, v_info_1171_);
lean_ctor_set(v___x_1176_, 1, v_openFence_1172_);
lean_ctor_set(v___x_1176_, 2, v___x_1175_);
lean_ctor_set(v___x_1176_, 3, v_lines_1173_);
v_z_1177_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushChild(v_s_1163_, v_z_1164_, v___x_1176_);
v_document_1178_ = lean_ctor_get(v_z_1177_, 0);
v_spine_1179_ = lean_ctor_get(v_z_1177_, 1);
v_blankLineFloor_x3f_1180_ = lean_ctor_get(v_z_1177_, 3);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_z_1177_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v_z_1177_, 2);
lean_dec(v_unused_1189_);
v___x_1182_ = v_z_1177_;
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_blankLineFloor_x3f_1180_);
lean_inc(v_spine_1179_);
lean_inc(v_document_1178_);
lean_dec(v_z_1177_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = lean_box(0);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 2, v___x_1184_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_document_1178_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_spine_1179_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_blankLineFloor_x3f_1180_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_del_object(v___x_1169_);
lean_dec(v_val_1167_);
lean_dec_ref(v_closeFence_1165_);
return v_z_1164_;
}
}
}
else
{
lean_dec(v_openLeaf_x3f_1166_);
lean_dec_ref(v_closeFence_1165_);
return v_z_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_closeFencedCode___boxed(lean_object* v_s_1192_, lean_object* v_z_1193_, lean_object* v_closeFence_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Markdown_BlockZipper_closeFencedCode(v_s_1192_, v_z_1193_, v_closeFence_1194_);
lean_dec_ref(v_s_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddLine___redArg(lean_object* v_z_1198_, lean_object* v_line_1199_){
_start:
{
lean_object* v_document_1200_; lean_object* v_spine_1201_; lean_object* v_openLeaf_x3f_1202_; lean_object* v_blankLineFloor_x3f_1203_; lean_object* v___y_1205_; 
v_document_1200_ = lean_ctor_get(v_z_1198_, 0);
v_spine_1201_ = lean_ctor_get(v_z_1198_, 1);
v_openLeaf_x3f_1202_ = lean_ctor_get(v_z_1198_, 2);
v_blankLineFloor_x3f_1203_ = lean_ctor_get(v_z_1198_, 3);
if (lean_obj_tag(v_openLeaf_x3f_1202_) == 0)
{
lean_dec_ref(v_line_1199_);
return v_z_1198_;
}
else
{
lean_object* v_val_1208_; 
lean_inc_ref(v_openLeaf_x3f_1202_);
lean_inc(v_blankLineFloor_x3f_1203_);
lean_inc_ref(v_spine_1201_);
lean_inc_ref(v_document_1200_);
lean_dec_ref(v_z_1198_);
v_val_1208_ = lean_ctor_get(v_openLeaf_x3f_1202_, 0);
lean_inc(v_val_1208_);
lean_dec_ref_known(v_openLeaf_x3f_1202_, 1);
if (lean_obj_tag(v_val_1208_) == 2)
{
lean_object* v_lines_1209_; lean_object* v_pendingBlanks_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1220_; 
v_lines_1209_ = lean_ctor_get(v_val_1208_, 0);
v_pendingBlanks_1210_ = lean_ctor_get(v_val_1208_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_val_1208_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1212_ = v_val_1208_;
v_isShared_1213_ = v_isSharedCheck_1220_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_pendingBlanks_1210_);
lean_inc(v_lines_1209_);
lean_dec(v_val_1208_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1220_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1214_ = l_Array_append___redArg(v_lines_1209_, v_pendingBlanks_1210_);
lean_dec_ref(v_pendingBlanks_1210_);
v___x_1215_ = lean_array_push(v___x_1214_, v_line_1199_);
v___x_1216_ = ((lean_object*)(l_Lean_Markdown_BlockZipper_indentedCodeAddLine___redArg___closed__0));
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___x_1216_);
lean_ctor_set(v___x_1212_, 0, v___x_1215_);
v___x_1218_ = v___x_1212_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
v___y_1205_ = v___x_1218_;
goto v___jp_1204_;
}
}
}
else
{
lean_dec_ref(v_line_1199_);
v___y_1205_ = v_val_1208_;
goto v___jp_1204_;
}
}
v___jp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___y_1205_);
v___x_1207_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1207_, 0, v_document_1200_);
lean_ctor_set(v___x_1207_, 1, v_spine_1201_);
lean_ctor_set(v___x_1207_, 2, v___x_1206_);
lean_ctor_set(v___x_1207_, 3, v_blankLineFloor_x3f_1203_);
return v___x_1207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddLine(lean_object* v_s_1221_, lean_object* v_z_1222_, lean_object* v_line_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Markdown_BlockZipper_indentedCodeAddLine___redArg(v_z_1222_, v_line_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddLine___boxed(lean_object* v_s_1225_, lean_object* v_z_1226_, lean_object* v_line_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_Markdown_BlockZipper_indentedCodeAddLine(v_s_1225_, v_z_1226_, v_line_1227_);
lean_dec_ref(v_s_1225_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddBlank___redArg(lean_object* v_z_1229_, lean_object* v_line_1230_){
_start:
{
lean_object* v_document_1231_; lean_object* v_spine_1232_; lean_object* v_openLeaf_x3f_1233_; lean_object* v_blankLineFloor_x3f_1234_; lean_object* v___y_1236_; 
v_document_1231_ = lean_ctor_get(v_z_1229_, 0);
v_spine_1232_ = lean_ctor_get(v_z_1229_, 1);
v_openLeaf_x3f_1233_ = lean_ctor_get(v_z_1229_, 2);
v_blankLineFloor_x3f_1234_ = lean_ctor_get(v_z_1229_, 3);
if (lean_obj_tag(v_openLeaf_x3f_1233_) == 0)
{
lean_dec_ref(v_line_1230_);
return v_z_1229_;
}
else
{
lean_object* v_val_1239_; 
lean_inc_ref(v_openLeaf_x3f_1233_);
lean_inc(v_blankLineFloor_x3f_1234_);
lean_inc_ref(v_spine_1232_);
lean_inc_ref(v_document_1231_);
lean_dec_ref(v_z_1229_);
v_val_1239_ = lean_ctor_get(v_openLeaf_x3f_1233_, 0);
lean_inc(v_val_1239_);
lean_dec_ref_known(v_openLeaf_x3f_1233_, 1);
if (lean_obj_tag(v_val_1239_) == 2)
{
lean_object* v_lines_1240_; lean_object* v_pendingBlanks_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1249_; 
v_lines_1240_ = lean_ctor_get(v_val_1239_, 0);
v_pendingBlanks_1241_ = lean_ctor_get(v_val_1239_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_val_1239_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1243_ = v_val_1239_;
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_pendingBlanks_1241_);
lean_inc(v_lines_1240_);
lean_dec(v_val_1239_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = lean_array_push(v_pendingBlanks_1241_, v_line_1230_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1245_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_lines_1240_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
v___y_1236_ = v___x_1247_;
goto v___jp_1235_;
}
}
}
else
{
lean_dec_ref(v_line_1230_);
v___y_1236_ = v_val_1239_;
goto v___jp_1235_;
}
}
v___jp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___y_1236_);
v___x_1238_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1238_, 0, v_document_1231_);
lean_ctor_set(v___x_1238_, 1, v_spine_1232_);
lean_ctor_set(v___x_1238_, 2, v___x_1237_);
lean_ctor_set(v___x_1238_, 3, v_blankLineFloor_x3f_1234_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddBlank(lean_object* v_s_1250_, lean_object* v_z_1251_, lean_object* v_line_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Markdown_BlockZipper_indentedCodeAddBlank___redArg(v_z_1251_, v_line_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddBlank___boxed(lean_object* v_s_1254_, lean_object* v_z_1255_, lean_object* v_line_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Markdown_BlockZipper_indentedCodeAddBlank(v_s_1254_, v_z_1255_, v_line_1256_);
lean_dec_ref(v_s_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_pushBlockquoteMarker___redArg(lean_object* v_z_1258_, lean_object* v_i_1259_, lean_object* v_m_1260_){
_start:
{
lean_object* v_document_1261_; lean_object* v_spine_1262_; lean_object* v_openLeaf_x3f_1263_; lean_object* v_blankLineFloor_x3f_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1303_; 
v_document_1261_ = lean_ctor_get(v_z_1258_, 0);
v_spine_1262_ = lean_ctor_get(v_z_1258_, 1);
v_openLeaf_x3f_1263_ = lean_ctor_get(v_z_1258_, 2);
v_blankLineFloor_x3f_1264_ = lean_ctor_get(v_z_1258_, 3);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_z_1258_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1266_ = v_z_1258_;
v_isShared_1267_ = v_isSharedCheck_1303_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_blankLineFloor_x3f_1264_);
lean_inc(v_openLeaf_x3f_1263_);
lean_inc(v_spine_1262_);
lean_inc(v_document_1261_);
lean_dec(v_z_1258_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1303_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = lean_array_get_size(v_spine_1262_);
v___x_1269_ = lean_nat_dec_lt(v_i_1259_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1271_; 
lean_dec_ref(v_m_1260_);
if (v_isShared_1267_ == 0)
{
v___x_1271_ = v___x_1266_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_document_1261_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_spine_1262_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_openLeaf_x3f_1263_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v_blankLineFloor_x3f_1264_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
else
{
lean_object* v_v_1273_; lean_object* v_container_1274_; lean_object* v_children_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1302_; 
v_v_1273_ = lean_array_fget(v_spine_1262_, v_i_1259_);
v_container_1274_ = lean_ctor_get(v_v_1273_, 0);
v_children_1275_ = lean_ctor_get(v_v_1273_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_v_1273_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1277_ = v_v_1273_;
v_isShared_1278_ = v_isSharedCheck_1302_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_children_1275_);
lean_inc(v_container_1274_);
lean_dec(v_v_1273_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1302_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; lean_object* v_xs_x27_1280_; lean_object* v___y_1282_; 
v___x_1279_ = lean_box(0);
v_xs_x27_1280_ = lean_array_fset(v_spine_1262_, v_i_1259_, v___x_1279_);
if (lean_obj_tag(v_container_1274_) == 0)
{
lean_object* v_markers_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1298_; 
v_markers_1287_ = lean_ctor_get(v_container_1274_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_container_1274_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1289_ = v_container_1274_;
v_isShared_1290_ = v_isSharedCheck_1298_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_markers_1287_);
lean_dec(v_container_1274_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1298_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1291_ = lean_array_push(v_markers_1287_, v_m_1260_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1291_);
v___x_1293_ = v___x_1289_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1295_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1293_);
v___x_1295_ = v___x_1277_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_children_1275_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
v___y_1282_ = v___x_1295_;
goto v___jp_1281_;
}
}
}
}
else
{
lean_object* v___x_1300_; 
lean_dec_ref(v_m_1260_);
if (v_isShared_1278_ == 0)
{
v___x_1300_ = v___x_1277_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_container_1274_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_children_1275_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
v___y_1282_ = v___x_1300_;
goto v___jp_1281_;
}
}
v___jp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1283_ = lean_array_fset(v_xs_x27_1280_, v_i_1259_, v___y_1282_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1283_);
v___x_1285_ = v___x_1266_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_document_1261_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_openLeaf_x3f_1263_);
lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_blankLineFloor_x3f_1264_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_pushBlockquoteMarker___redArg___boxed(lean_object* v_z_1304_, lean_object* v_i_1305_, lean_object* v_m_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_Markdown_BlockZipper_pushBlockquoteMarker___redArg(v_z_1304_, v_i_1305_, v_m_1306_);
lean_dec(v_i_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_pushBlockquoteMarker(lean_object* v_s_1308_, lean_object* v_z_1309_, lean_object* v_i_1310_, lean_object* v_m_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Markdown_BlockZipper_pushBlockquoteMarker___redArg(v_z_1309_, v_i_1310_, v_m_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_pushBlockquoteMarker___boxed(lean_object* v_s_1313_, lean_object* v_z_1314_, lean_object* v_i_1315_, lean_object* v_m_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Markdown_BlockZipper_pushBlockquoteMarker(v_s_1313_, v_z_1314_, v_i_1315_, v_m_1316_);
lean_dec(v_i_1315_);
lean_dec_ref(v_s_1313_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushBlockquoteMarker_match__1_splitter___redArg(lean_object* v_x_1318_, lean_object* v_h__1_1319_, lean_object* v_h__2_1320_){
_start:
{
lean_object* v_container_1321_; 
v_container_1321_ = lean_ctor_get(v_x_1318_, 0);
lean_inc_ref(v_container_1321_);
if (lean_obj_tag(v_container_1321_) == 0)
{
lean_object* v_children_1322_; lean_object* v_markers_1323_; lean_object* v___x_1324_; 
lean_dec(v_h__2_1320_);
v_children_1322_ = lean_ctor_get(v_x_1318_, 1);
lean_inc_ref(v_children_1322_);
lean_dec_ref(v_x_1318_);
v_markers_1323_ = lean_ctor_get(v_container_1321_, 0);
lean_inc_ref(v_markers_1323_);
lean_dec_ref_known(v_container_1321_, 1);
v___x_1324_ = lean_apply_2(v_h__1_1319_, v_markers_1323_, v_children_1322_);
return v___x_1324_;
}
else
{
lean_object* v_children_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v_h__1_1319_);
v_children_1325_ = lean_ctor_get(v_x_1318_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_x_1318_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_x_1318_, 0);
lean_dec(v_unused_1334_);
v___x_1327_ = v_x_1318_;
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_children_1325_);
lean_dec(v_x_1318_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1333_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_container_1321_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_children_1325_);
v___x_1330_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_apply_2(v_h__2_1320_, v___x_1330_, lean_box(0));
return v___x_1331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushBlockquoteMarker_match__1_splitter(lean_object* v_s_1335_, lean_object* v_motive_1336_, lean_object* v_x_1337_, lean_object* v_h__1_1338_, lean_object* v_h__2_1339_){
_start:
{
lean_object* v_container_1340_; 
v_container_1340_ = lean_ctor_get(v_x_1337_, 0);
lean_inc_ref(v_container_1340_);
if (lean_obj_tag(v_container_1340_) == 0)
{
lean_object* v_children_1341_; lean_object* v_markers_1342_; lean_object* v___x_1343_; 
lean_dec(v_h__2_1339_);
v_children_1341_ = lean_ctor_get(v_x_1337_, 1);
lean_inc_ref(v_children_1341_);
lean_dec_ref(v_x_1337_);
v_markers_1342_ = lean_ctor_get(v_container_1340_, 0);
lean_inc_ref(v_markers_1342_);
lean_dec_ref_known(v_container_1340_, 1);
v___x_1343_ = lean_apply_2(v_h__1_1338_, v_markers_1342_, v_children_1341_);
return v___x_1343_;
}
else
{
lean_object* v_children_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_h__1_1338_);
v_children_1344_ = lean_ctor_get(v_x_1337_, 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_x_1337_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v_x_1337_, 0);
lean_dec(v_unused_1353_);
v___x_1346_ = v_x_1337_;
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_children_1344_);
lean_dec(v_x_1337_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_container_1340_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_children_1344_);
v___x_1349_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_apply_2(v_h__2_1339_, v___x_1349_, lean_box(0));
return v___x_1350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushBlockquoteMarker_match__1_splitter___boxed(lean_object* v_s_1354_, lean_object* v_motive_1355_, lean_object* v_x_1356_, lean_object* v_h__1_1357_, lean_object* v_h__2_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l___private_Lean_Data_Markdown_Parser_BlockZipper_0__Lean_Markdown_BlockZipper_pushBlockquoteMarker_match__1_splitter(v_s_1354_, v_motive_1355_, v_x_1356_, v_h__1_1357_, v_h__2_1358_);
lean_dec_ref(v_s_1354_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0___redArg(lean_object* v_s_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_spine_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_spine_1362_ = lean_ctor_get(v_a_1361_, 1);
v___x_1363_ = lean_array_get_size(v_spine_1362_);
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_nat_dec_eq(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_Markdown_BlockZipper_closeContainer(v_s_1360_, v_a_1361_);
v_a_1361_ = v___x_1366_;
goto _start;
}
else
{
return v_a_1361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0___redArg___boxed(lean_object* v_s_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0___redArg(v_s_1368_, v_a_1369_);
lean_dec_ref(v_s_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_finalize(lean_object* v_s_1371_, lean_object* v_z_1372_){
_start:
{
lean_object* v_z_1373_; lean_object* v___x_1374_; lean_object* v_document_1375_; lean_object* v___x_1376_; lean_object* v_blocks_1377_; 
v_z_1373_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_1371_, v_z_1372_);
v___x_1374_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0___redArg(v_s_1371_, v_z_1373_);
v_document_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref(v_document_1375_);
lean_dec_ref(v___x_1374_);
v___x_1376_ = l_Lean_Markdown_Children_flushLists(v_s_1371_, v_document_1375_);
v_blocks_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref(v_blocks_1377_);
lean_dec_ref(v___x_1376_);
return v_blocks_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_BlockZipper_finalize___boxed(lean_object* v_s_1378_, lean_object* v_z_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lean_Markdown_BlockZipper_finalize(v_s_1378_, v_z_1379_);
lean_dec_ref(v_s_1378_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0(lean_object* v_s_1381_, lean_object* v_inst_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0___redArg(v_s_1381_, v_a_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0___boxed(lean_object* v_s_1385_, lean_object* v_inst_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_BlockZipper_finalize_spec__0(v_s_1385_, v_inst_1386_, v_a_1387_);
lean_dec_ref(v_s_1385_);
return v_res_1388_;
}
}
lean_object* runtime_initialize_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Block(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Html(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Children(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_InlineSource(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Parser_BlockZipper(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_Html(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_Children(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_InlineSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Parser_BlockZipper(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Block(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Parser_Html(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Parser_Children(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_InlineSource(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Parser_BlockZipper(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Parser_Html(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Parser_Children(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_InlineSource(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_BlockZipper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Parser_BlockZipper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Parser_BlockZipper(builtin);
}
#ifdef __cplusplus
}
#endif
