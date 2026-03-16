// Lean compiler output
// Module: Lean.Elab.Quotation.Util
// Imports: public import Lean.Elab.Term
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object*);
lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_topDown(lean_object*, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hygiene"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(187, 171, 26, 124, 58, 231, 48, 110)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 243, .m_capacity = 243, .m_length = 242, .m_data = "Annotate identifiers in quotations such that they are resolved relative to the scope at their declaration, not that at their eventual use/expansion, to avoid accidental capturing. Note that quotations/notations already defined are unaffected."};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Quotation"};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(66, 249, 245, 72, 137, 60, 151, 235)}};
static const lean_object* l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_hygiene;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__0 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1_value;
static const lean_string_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__3 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__3_value;
static const lean_string_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value;
static const lean_string_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "complex antiquotation not allowed here"};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__5 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__5_value;
static lean_once_cell_t l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___closed__0 = (const lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___closed__1 = (const lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "namedPattern"};
static const lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___closed__2 = (const lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_0),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 38, 53, 234, 94, 148, 183, 69)}};
static const lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___closed__3 = (const lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value;
static const lean_string_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "unsupported pattern in syntax match"};
static const lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___closed__4 = (const lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_));
v___x_61_ = l_Lean_Option_register___at___00Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1(lean_object* v_msgData_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; lean_object* v_env_71_; lean_object* v___x_72_; lean_object* v_mctx_73_; lean_object* v_lctx_74_; lean_object* v_options_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_70_ = lean_st_ref_get(v___y_68_);
v_env_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_env_71_);
lean_dec(v___x_70_);
v___x_72_ = lean_st_ref_get(v___y_66_);
v_mctx_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc_ref(v_mctx_73_);
lean_dec(v___x_72_);
v_lctx_74_ = lean_ctor_get(v___y_65_, 2);
v_options_75_ = lean_ctor_get(v___y_67_, 2);
lean_inc_ref(v_options_75_);
lean_inc_ref(v_lctx_74_);
v___x_76_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_76_, 0, v_env_71_);
lean_ctor_set(v___x_76_, 1, v_mctx_73_);
lean_ctor_set(v___x_76_, 2, v_lctx_74_);
lean_ctor_set(v___x_76_, 3, v_options_75_);
v___x_77_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v_msgData_64_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1(v_msgData_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_85_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4(lean_object* v_opts_86_, lean_object* v_opt_87_){
_start:
{
lean_object* v_name_88_; lean_object* v_defValue_89_; lean_object* v_map_90_; lean_object* v___x_91_; 
v_name_88_ = lean_ctor_get(v_opt_87_, 0);
v_defValue_89_ = lean_ctor_get(v_opt_87_, 1);
v_map_90_ = lean_ctor_get(v_opts_86_, 0);
v___x_91_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_90_, v_name_88_);
if (lean_obj_tag(v___x_91_) == 0)
{
uint8_t v___x_92_; 
v___x_92_ = lean_unbox(v_defValue_89_);
return v___x_92_;
}
else
{
lean_object* v_val_93_; 
v_val_93_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_val_93_);
lean_dec_ref(v___x_91_);
if (lean_obj_tag(v_val_93_) == 1)
{
uint8_t v_v_94_; 
v_v_94_ = lean_ctor_get_uint8(v_val_93_, 0);
lean_dec_ref(v_val_93_);
return v_v_94_;
}
else
{
uint8_t v___x_95_; 
lean_dec(v_val_93_);
v___x_95_ = lean_unbox(v_defValue_89_);
return v___x_95_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_opts_96_, lean_object* v_opt_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4(v_opts_96_, v_opt_97_);
lean_dec_ref(v_opt_97_);
lean_dec_ref(v_opts_96_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_box(1);
v___x_101_ = l_Lean_MessageData_ofFormat(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__2));
v___x_106_ = l_Lean_MessageData_ofFormat(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
return v_x_107_;
}
else
{
lean_object* v_head_109_; lean_object* v_tail_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_132_; 
v_head_109_ = lean_ctor_get(v_x_108_, 0);
v_tail_110_ = lean_ctor_get(v_x_108_, 1);
v_isSharedCheck_132_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_132_ == 0)
{
v___x_112_ = v_x_108_;
v_isShared_113_ = v_isSharedCheck_132_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_tail_110_);
lean_inc(v_head_109_);
lean_dec(v_x_108_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_132_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_before_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_130_; 
v_before_114_ = lean_ctor_get(v_head_109_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v_head_109_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; 
v_unused_131_ = lean_ctor_get(v_head_109_, 1);
lean_dec(v_unused_131_);
v___x_116_ = v_head_109_;
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_before_114_);
lean_dec(v_head_109_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_118_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 7);
lean_ctor_set(v___x_116_, 1, v___x_118_);
lean_ctor_set(v___x_116_, 0, v_x_107_);
v___x_120_ = v___x_116_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_x_107_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_118_);
v___x_120_ = v_reuseFailAlloc_129_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_121_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 7);
lean_ctor_set(v___x_112_, 1, v___x_121_);
lean_ctor_set(v___x_112_, 0, v___x_120_);
v___x_123_ = v___x_112_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_121_);
v___x_123_ = v_reuseFailAlloc_128_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = l_Lean_MessageData_ofSyntax(v_before_114_);
v___x_125_ = l_Lean_indentD(v___x_124_);
v___x_126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_123_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v_x_107_ = v___x_126_;
v_x_108_ = v_tail_110_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_137_ = l_Lean_MessageData_ofFormat(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_138_, lean_object* v_macroStack_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_options_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_options_142_ = lean_ctor_get(v___y_140_, 2);
v___x_143_ = l_Lean_Elab_pp_macroStack;
v___x_144_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4(v_options_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
lean_dec(v_macroStack_139_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v_msgData_138_);
return v___x_145_;
}
else
{
if (lean_obj_tag(v_macroStack_139_) == 0)
{
lean_object* v___x_146_; 
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v_msgData_138_);
return v___x_146_;
}
else
{
lean_object* v_head_147_; lean_object* v_after_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_163_; 
v_head_147_ = lean_ctor_get(v_macroStack_139_, 0);
lean_inc(v_head_147_);
v_after_148_ = lean_ctor_get(v_head_147_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_head_147_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; 
v_unused_164_ = lean_ctor_get(v_head_147_, 0);
lean_dec(v_unused_164_);
v___x_150_ = v_head_147_;
v_isShared_151_ = v_isSharedCheck_163_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_after_148_);
lean_dec(v_head_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_163_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_151_ == 0)
{
lean_ctor_set_tag(v___x_150_, 7);
lean_ctor_set(v___x_150_, 1, v___x_152_);
lean_ctor_set(v___x_150_, 0, v_msgData_138_);
v___x_154_ = v___x_150_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_msgData_138_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_162_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_msgData_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_155_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = l_Lean_MessageData_ofSyntax(v_after_148_);
v___x_158_ = l_Lean_indentD(v___x_157_);
v_msgData_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_159_, 0, v___x_156_);
lean_ctor_set(v_msgData_159_, 1, v___x_158_);
v___x_160_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5(v_msgData_159_, v_macroStack_139_);
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_165_, lean_object* v_macroStack_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_msgData_165_, v_macroStack_166_, v___y_167_);
lean_dec_ref(v___y_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_ref_178_; lean_object* v___x_179_; lean_object* v_a_180_; lean_object* v_macroStack_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_192_; 
v_ref_178_ = lean_ctor_get(v___y_175_, 5);
v___x_179_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1(v_msg_170_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref(v___x_179_);
v_macroStack_181_ = lean_ctor_get(v___y_171_, 1);
lean_inc(v_macroStack_181_);
lean_dec_ref(v___y_171_);
lean_inc(v_macroStack_181_);
v___x_182_ = l_Lean_Elab_getBetterRef(v_ref_178_, v_macroStack_181_);
v___x_183_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_a_180_, v_macroStack_181_, v___y_175_);
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_192_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_182_);
lean_ctor_set(v___x_188_, 1, v_a_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 1);
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg___boxed(lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(lean_object* v_ref_202_, lean_object* v_msg_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_fileName_211_; lean_object* v_fileMap_212_; lean_object* v_options_213_; lean_object* v_currRecDepth_214_; lean_object* v_maxRecDepth_215_; lean_object* v_ref_216_; lean_object* v_currNamespace_217_; lean_object* v_openDecls_218_; lean_object* v_initHeartbeats_219_; lean_object* v_maxHeartbeats_220_; lean_object* v_quotContext_221_; lean_object* v_currMacroScope_222_; uint8_t v_diag_223_; lean_object* v_cancelTk_x3f_224_; uint8_t v_suppressElabErrors_225_; lean_object* v_inheritedTraceOptions_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_235_; 
v_fileName_211_ = lean_ctor_get(v___y_208_, 0);
v_fileMap_212_ = lean_ctor_get(v___y_208_, 1);
v_options_213_ = lean_ctor_get(v___y_208_, 2);
v_currRecDepth_214_ = lean_ctor_get(v___y_208_, 3);
v_maxRecDepth_215_ = lean_ctor_get(v___y_208_, 4);
v_ref_216_ = lean_ctor_get(v___y_208_, 5);
v_currNamespace_217_ = lean_ctor_get(v___y_208_, 6);
v_openDecls_218_ = lean_ctor_get(v___y_208_, 7);
v_initHeartbeats_219_ = lean_ctor_get(v___y_208_, 8);
v_maxHeartbeats_220_ = lean_ctor_get(v___y_208_, 9);
v_quotContext_221_ = lean_ctor_get(v___y_208_, 10);
v_currMacroScope_222_ = lean_ctor_get(v___y_208_, 11);
v_diag_223_ = lean_ctor_get_uint8(v___y_208_, sizeof(void*)*14);
v_cancelTk_x3f_224_ = lean_ctor_get(v___y_208_, 12);
v_suppressElabErrors_225_ = lean_ctor_get_uint8(v___y_208_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_226_ = lean_ctor_get(v___y_208_, 13);
v_isSharedCheck_235_ = !lean_is_exclusive(v___y_208_);
if (v_isSharedCheck_235_ == 0)
{
v___x_228_ = v___y_208_;
v_isShared_229_ = v_isSharedCheck_235_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_inheritedTraceOptions_226_);
lean_inc(v_cancelTk_x3f_224_);
lean_inc(v_currMacroScope_222_);
lean_inc(v_quotContext_221_);
lean_inc(v_maxHeartbeats_220_);
lean_inc(v_initHeartbeats_219_);
lean_inc(v_openDecls_218_);
lean_inc(v_currNamespace_217_);
lean_inc(v_ref_216_);
lean_inc(v_maxRecDepth_215_);
lean_inc(v_currRecDepth_214_);
lean_inc(v_options_213_);
lean_inc(v_fileMap_212_);
lean_inc(v_fileName_211_);
lean_dec(v___y_208_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_235_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_ref_230_; lean_object* v___x_232_; 
v_ref_230_ = l_Lean_replaceRef(v_ref_202_, v_ref_216_);
lean_dec(v_ref_216_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 5, v_ref_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_fileName_211_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_fileMap_212_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_options_213_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_currRecDepth_214_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v_maxRecDepth_215_);
lean_ctor_set(v_reuseFailAlloc_234_, 5, v_ref_230_);
lean_ctor_set(v_reuseFailAlloc_234_, 6, v_currNamespace_217_);
lean_ctor_set(v_reuseFailAlloc_234_, 7, v_openDecls_218_);
lean_ctor_set(v_reuseFailAlloc_234_, 8, v_initHeartbeats_219_);
lean_ctor_set(v_reuseFailAlloc_234_, 9, v_maxHeartbeats_220_);
lean_ctor_set(v_reuseFailAlloc_234_, 10, v_quotContext_221_);
lean_ctor_set(v_reuseFailAlloc_234_, 11, v_currMacroScope_222_);
lean_ctor_set(v_reuseFailAlloc_234_, 12, v_cancelTk_x3f_224_);
lean_ctor_set(v_reuseFailAlloc_234_, 13, v_inheritedTraceOptions_226_);
lean_ctor_set_uint8(v_reuseFailAlloc_234_, sizeof(void*)*14, v_diag_223_);
lean_ctor_set_uint8(v_reuseFailAlloc_234_, sizeof(void*)*14 + 1, v_suppressElabErrors_225_);
v___x_232_ = v_reuseFailAlloc_234_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___x_232_, v___y_209_);
lean_dec_ref(v___x_232_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg___boxed(lean_object* v_ref_236_, lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_ref_236_, v_msg_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec(v_ref_236_);
return v_res_245_;
}
}
static lean_object* _init_l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__5));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(uint8_t v_firstChoiceOnly_259_, lean_object* v_stx_260_, lean_object* v_b_261_, lean_object* v_inst_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_b_271_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v_a_302_; uint8_t v___x_329_; 
v___x_329_ = l_Lean_Syntax_isAntiquot(v_stx_260_);
if (v___x_329_ == 0)
{
uint8_t v___x_330_; 
lean_inc(v_stx_260_);
v___x_330_ = l_Lean_Syntax_isTokenAntiquot(v_stx_260_);
if (v___x_330_ == 0)
{
v_a_302_ = v_b_261_;
goto v___jp_301_;
}
else
{
goto v___jp_312_;
}
}
else
{
goto v___jp_312_;
}
v___jp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_b_271_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
v___jp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; size_t v_sz_279_; size_t v___x_280_; lean_object* v___x_281_; 
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___y_276_);
v_sz_279_ = lean_array_size(v___y_275_);
v___x_280_ = ((size_t)0ULL);
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(v_firstChoiceOnly_259_, v_inst_262_, v___y_275_, v_sz_279_, v___x_280_, v___x_278_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec_ref(v___y_275_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_292_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_292_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_292_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_292_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_fst_286_; 
v_fst_286_ = lean_ctor_get(v_a_282_, 0);
if (lean_obj_tag(v_fst_286_) == 0)
{
lean_object* v_snd_287_; 
lean_del_object(v___x_284_);
v_snd_287_ = lean_ctor_get(v_a_282_, 1);
lean_inc(v_snd_287_);
lean_dec(v_a_282_);
v_b_271_ = v_snd_287_;
goto v___jp_270_;
}
else
{
lean_object* v_val_288_; lean_object* v___x_290_; 
lean_inc_ref(v_fst_286_);
lean_dec(v_a_282_);
v_val_288_ = lean_ctor_get(v_fst_286_, 0);
lean_inc(v_val_288_);
lean_dec_ref(v_fst_286_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v_val_288_);
v___x_290_ = v___x_284_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_val_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
v_a_293_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_281_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_281_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
v___jp_301_:
{
if (lean_obj_tag(v_stx_260_) == 1)
{
if (v_firstChoiceOnly_259_ == 0)
{
lean_object* v_args_303_; 
v_args_303_ = lean_ctor_get(v_stx_260_, 2);
lean_inc_ref(v_args_303_);
lean_dec_ref(v_stx_260_);
v___y_275_ = v_args_303_;
v___y_276_ = v_a_302_;
goto v___jp_274_;
}
else
{
lean_object* v_kind_304_; lean_object* v_args_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_kind_304_ = lean_ctor_get(v_stx_260_, 1);
lean_inc(v_kind_304_);
v_args_305_ = lean_ctor_get(v_stx_260_, 2);
lean_inc_ref(v_args_305_);
lean_dec_ref(v_stx_260_);
v___x_306_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1));
v___x_307_ = lean_name_eq(v_kind_304_, v___x_306_);
lean_dec(v_kind_304_);
if (v___x_307_ == 0)
{
v___y_275_ = v_args_305_;
v___y_276_ = v_a_302_;
goto v___jp_274_;
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_box(0);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_array_get(v___x_308_, v_args_305_, v___x_309_);
lean_dec_ref(v_args_305_);
v_stx_260_ = v___x_310_;
v_b_261_ = v_a_302_;
goto _start;
}
}
}
else
{
lean_dec_ref(v___y_267_);
lean_dec_ref(v___y_263_);
lean_dec(v_stx_260_);
v_b_271_ = v_a_302_;
goto v___jp_270_;
}
}
v___jp_312_:
{
uint8_t v___x_313_; 
v___x_313_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_260_);
if (v___x_313_ == 0)
{
lean_object* v_anti_314_; uint8_t v___x_315_; 
v_anti_314_ = l_Lean_Syntax_getAntiquotTerm(v_stx_260_);
v___x_315_ = l_Lean_Syntax_isIdent(v_anti_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_316_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4));
v___x_317_ = l_Lean_Syntax_isOfKind(v_anti_314_, v___x_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_obj_once(&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6, &l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6_once, _init_l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6);
lean_inc_ref(v___y_267_);
lean_inc_ref(v___y_263_);
v___x_319_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_260_, v___x_318_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_dec_ref(v___x_319_);
v_a_302_ = v_b_261_;
goto v___jp_301_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v___y_267_);
lean_dec_ref(v___y_263_);
lean_dec_ref(v_b_261_);
lean_dec(v_stx_260_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
v_a_302_ = v_b_261_;
goto v___jp_301_;
}
}
else
{
lean_object* v_ids_328_; 
v_ids_328_ = lean_array_push(v_b_261_, v_anti_314_);
v_a_302_ = v_ids_328_;
goto v___jp_301_;
}
}
else
{
v_a_302_ = v_b_261_;
goto v___jp_301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(uint8_t v_firstChoiceOnly_331_, lean_object* v_inst_332_, lean_object* v_as_333_, size_t v_sz_334_, size_t v_i_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
uint8_t v___x_344_; 
v___x_344_ = lean_usize_dec_lt(v_i_335_, v_sz_334_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
lean_dec_ref(v___y_341_);
lean_dec_ref(v___y_337_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v_b_336_);
return v___x_345_;
}
else
{
lean_object* v_snd_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_380_; 
v_snd_346_ = lean_ctor_get(v_b_336_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_b_336_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_b_336_, 0);
lean_dec(v_unused_381_);
v___x_348_ = v_b_336_;
v_isShared_349_ = v_isSharedCheck_380_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snd_346_);
lean_dec(v_b_336_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_380_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_a_350_; lean_object* v___x_351_; 
v_a_350_ = lean_array_uget_borrowed(v_as_333_, v_i_335_);
lean_inc_ref(v___y_341_);
lean_inc_ref(v___y_337_);
lean_inc(v_snd_346_);
lean_inc(v_a_350_);
v___x_351_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_331_, v_a_350_, v_snd_346_, v_inst_332_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_371_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_371_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_371_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_371_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
if (lean_obj_tag(v_a_352_) == 0)
{
lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec_ref(v___y_341_);
lean_dec_ref(v___y_337_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v_a_352_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_356_);
v___x_358_ = v___x_348_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_snd_346_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_358_);
v___x_360_ = v___x_354_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
lean_del_object(v___x_354_);
lean_dec(v_snd_346_);
v_a_363_ = lean_ctor_get(v_a_352_, 0);
lean_inc(v_a_363_);
lean_dec_ref(v_a_352_);
v___x_364_ = lean_box(0);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v_a_363_);
lean_ctor_set(v___x_348_, 0, v___x_364_);
v___x_366_ = v___x_348_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_a_363_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
size_t v___x_367_; size_t v___x_368_; 
v___x_367_ = ((size_t)1ULL);
v___x_368_ = lean_usize_add(v_i_335_, v___x_367_);
v_i_335_ = v___x_368_;
v_b_336_ = v___x_366_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_del_object(v___x_348_);
lean_dec(v_snd_346_);
lean_dec_ref(v___y_341_);
lean_dec_ref(v___y_337_);
v_a_372_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_351_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_351_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2___boxed(lean_object* v_firstChoiceOnly_382_, lean_object* v_inst_383_, lean_object* v_as_384_, lean_object* v_sz_385_, lean_object* v_i_386_, lean_object* v_b_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_395_; size_t v_sz_boxed_396_; size_t v_i_boxed_397_; lean_object* v_res_398_; 
v_firstChoiceOnly_boxed_395_ = lean_unbox(v_firstChoiceOnly_382_);
v_sz_boxed_396_ = lean_unbox_usize(v_sz_385_);
lean_dec(v_sz_385_);
v_i_boxed_397_ = lean_unbox_usize(v_i_386_);
lean_dec(v_i_386_);
v_res_398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(v_firstChoiceOnly_boxed_395_, v_inst_383_, v_as_384_, v_sz_boxed_396_, v_i_boxed_397_, v_b_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v_as_384_);
lean_dec_ref(v_inst_383_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___boxed(lean_object* v_firstChoiceOnly_399_, lean_object* v_stx_400_, lean_object* v_b_401_, lean_object* v_inst_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_410_; lean_object* v_res_411_; 
v_firstChoiceOnly_boxed_410_ = lean_unbox(v_firstChoiceOnly_399_);
v_res_411_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_boxed_410_, v_stx_400_, v_b_401_, v_inst_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v_inst_402_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds(lean_object* v_stx_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
uint8_t v___x_422_; lean_object* v___x_423_; uint8_t v_firstChoiceOnly_424_; lean_object* v_stx_425_; lean_object* v_ids_426_; lean_object* v___x_427_; 
v___x_422_ = 1;
v___x_423_ = l_Lean_Syntax_topDown(v_stx_414_, v___x_422_);
v_firstChoiceOnly_424_ = lean_ctor_get_uint8(v___x_423_, sizeof(void*)*1);
v_stx_425_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_stx_425_);
lean_dec_ref(v___x_423_);
v_ids_426_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_427_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_424_, v_stx_425_, v_ids_426_, v_ids_426_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_436_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_436_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_a_432_; lean_object* v___x_434_; 
v_a_432_ = lean_ctor_get(v_a_428_, 0);
lean_inc(v_a_432_);
lean_dec(v_a_428_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v_a_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_a_437_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_427_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_427_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds___boxed(lean_object* v_stx_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds(v_stx_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(lean_object* v_00_u03b1_454_, lean_object* v_ref_455_, lean_object* v_msg_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_ref_455_, v_msg_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___boxed(lean_object* v_00_u03b1_465_, lean_object* v_ref_466_, lean_object* v_msg_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(v_00_u03b1_465_, v_ref_466_, v_msg_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec(v_ref_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(lean_object* v_00_u03b1_476_, lean_object* v_msg_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___boxed(lean_object* v_00_u03b1_486_, lean_object* v_msg_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(v_00_u03b1_486_, v_msg_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(lean_object* v_msgData_496_, lean_object* v_macroStack_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_msgData_496_, v_macroStack_497_, v___y_502_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_506_, lean_object* v_macroStack_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(v_msgData_506_, v_macroStack_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_515_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__4));
v___x_527_ = l_Lean_stringToMessageData(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternVars(lean_object* v_stx_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
uint8_t v___x_536_; 
v___x_536_ = l_Lean_Syntax_isQuot(v_stx_528_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4));
lean_inc(v_stx_528_);
v___x_538_ = l_Lean_Syntax_isOfKind(v_stx_528_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__1));
lean_inc(v_stx_528_);
v___x_540_ = l_Lean_Syntax_isOfKind(v_stx_528_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__3));
lean_inc(v_stx_528_);
v___x_542_ = l_Lean_Syntax_isOfKind(v_stx_528_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_543_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_528_);
v___x_544_ = l_Lean_MessageData_ofSyntax(v_stx_528_);
v___x_545_ = l_Lean_indentD(v___x_544_);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_543_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_528_, v___x_546_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_stx_528_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = l_Lean_Syntax_getArg(v_stx_528_, v___x_548_);
lean_inc(v___x_549_);
v___x_550_ = l_Lean_Syntax_isOfKind(v___x_549_, v___x_539_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec(v___x_549_);
v___x_551_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_528_);
v___x_552_ = l_Lean_MessageData_ofSyntax(v_stx_528_);
v___x_553_ = l_Lean_indentD(v___x_552_);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_551_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_528_, v___x_554_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_stx_528_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_556_ = lean_unsigned_to_nat(2u);
v___x_557_ = l_Lean_Syntax_getArg(v_stx_528_, v___x_556_);
v___x_558_ = l_Lean_Syntax_matchesNull(v___x_557_, v___x_548_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v___x_549_);
v___x_559_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_528_);
v___x_560_ = l_Lean_MessageData_ofSyntax(v_stx_528_);
v___x_561_ = l_Lean_indentD(v___x_560_);
v___x_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_559_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_528_, v___x_562_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_stx_528_);
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_unsigned_to_nat(3u);
v___x_565_ = l_Lean_Syntax_getArg(v_stx_528_, v___x_564_);
lean_dec(v_stx_528_);
v___x_566_ = l_Lean_Elab_Term_Quotation_getPatternVars(v___x_565_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_575_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_575_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_array_push(v_a_567_, v___x_549_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_571_);
v___x_573_ = v___x_569_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_dec(v___x_549_);
return v___x_566_;
}
}
}
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec_ref(v_a_533_);
lean_dec_ref(v_a_529_);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_mk_empty_array_with_capacity(v___x_576_);
v___x_578_ = lean_array_push(v___x_577_, v_stx_528_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec_ref(v_a_533_);
lean_dec_ref(v_a_529_);
lean_dec(v_stx_528_);
v___x_580_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
else
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds(v_stx_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
v_a_591_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_582_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_582_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___boxed(lean_object* v_stx_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Elab_Term_Quotation_getPatternVars(v_stx_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
lean_dec(v_a_605_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(lean_object* v_as_608_, size_t v_i_609_, size_t v_stop_610_, lean_object* v_b_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_a_620_; uint8_t v___x_624_; 
v___x_624_ = lean_usize_dec_eq(v_i_609_, v_stop_610_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_array_uget_borrowed(v_as_608_, v_i_609_);
lean_inc_ref(v___y_616_);
lean_inc_ref(v___y_612_);
lean_inc(v___x_625_);
v___x_626_ = l_Lean_Elab_Term_Quotation_getPatternVars(v___x_625_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_628_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref(v___x_626_);
v___x_628_ = l_Array_append___redArg(v_b_611_, v_a_627_);
lean_dec(v_a_627_);
v_a_620_ = v___x_628_;
goto v___jp_619_;
}
else
{
lean_dec_ref(v_b_611_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_629_; 
v_a_629_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_629_);
lean_dec_ref(v___x_626_);
v_a_620_ = v_a_629_;
goto v___jp_619_;
}
else
{
lean_dec_ref(v___y_616_);
lean_dec_ref(v___y_612_);
return v___x_626_;
}
}
}
else
{
lean_object* v___x_630_; 
lean_dec_ref(v___y_616_);
lean_dec_ref(v___y_612_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_b_611_);
return v___x_630_;
}
v___jp_619_:
{
size_t v___x_621_; size_t v___x_622_; 
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_add(v_i_609_, v___x_621_);
v_i_609_ = v___x_622_;
v_b_611_ = v_a_620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0___boxed(lean_object* v_as_631_, lean_object* v_i_632_, lean_object* v_stop_633_, lean_object* v_b_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
size_t v_i_boxed_642_; size_t v_stop_boxed_643_; lean_object* v_res_644_; 
v_i_boxed_642_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_stop_boxed_643_ = lean_unbox_usize(v_stop_633_);
lean_dec(v_stop_633_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_as_631_, v_i_boxed_642_, v_stop_boxed_643_, v_b_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v_as_631_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars(lean_object* v_pats_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_655_ = lean_array_get_size(v_pats_645_);
v___x_656_ = lean_nat_dec_lt(v___x_653_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec_ref(v_a_650_);
lean_dec_ref(v_a_646_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_654_);
return v___x_657_;
}
else
{
uint8_t v___x_658_; 
v___x_658_ = lean_nat_dec_le(v___x_655_, v___x_655_);
if (v___x_658_ == 0)
{
if (v___x_656_ == 0)
{
lean_object* v___x_659_; 
lean_dec_ref(v_a_650_);
lean_dec_ref(v_a_646_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_654_);
return v___x_659_;
}
else
{
size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; 
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_655_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_pats_645_, v___x_660_, v___x_661_, v___x_654_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
return v___x_662_;
}
}
else
{
size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_655_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_pats_645_, v___x_663_, v___x_664_, v___x_654_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
return v___x_665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars___boxed(lean_object* v_pats_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Elab_Term_Quotation_getPatternsVars(v_pats_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
lean_dec(v_a_672_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_pats_666_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(lean_object* v_antiquot_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_name_679_; uint8_t v___x_680_; 
v___x_676_ = lean_unsigned_to_nat(3u);
v___x_677_ = l_Lean_Syntax_getArg(v_antiquot_675_, v___x_676_);
v___x_678_ = lean_unsigned_to_nat(1u);
v_name_679_ = l_Lean_Syntax_getArg(v___x_677_, v___x_678_);
lean_dec(v___x_677_);
v___x_680_ = l_Lean_Syntax_isMissing(v_name_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v_name_679_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; 
lean_dec(v_name_679_);
v___x_682_ = lean_box(0);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f___boxed(lean_object* v_antiquot_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(v_antiquot_683_);
lean_dec(v_antiquot_683_);
return v_res_684_;
}
}
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Quotation_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_hygiene = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_hygiene);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Quotation_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Quotation_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Quotation_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Quotation_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Quotation_Util(builtin);
}
#ifdef __cplusplus
}
#endif
