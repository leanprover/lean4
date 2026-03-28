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
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
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
lean_inc_n(v_macroStack_181_, 2);
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
lean_dec_ref(v___y_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(lean_object* v_ref_202_, lean_object* v_msg_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_fileName_211_; lean_object* v_fileMap_212_; lean_object* v_options_213_; lean_object* v_currRecDepth_214_; lean_object* v_maxRecDepth_215_; lean_object* v_ref_216_; lean_object* v_currNamespace_217_; lean_object* v_openDecls_218_; lean_object* v_initHeartbeats_219_; lean_object* v_maxHeartbeats_220_; lean_object* v_quotContext_221_; lean_object* v_currMacroScope_222_; uint8_t v_diag_223_; lean_object* v_cancelTk_x3f_224_; uint8_t v_suppressElabErrors_225_; lean_object* v_inheritedTraceOptions_226_; lean_object* v_ref_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
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
v_ref_227_ = l_Lean_replaceRef(v_ref_202_, v_ref_216_);
lean_inc_ref(v_inheritedTraceOptions_226_);
lean_inc(v_cancelTk_x3f_224_);
lean_inc(v_currMacroScope_222_);
lean_inc(v_quotContext_221_);
lean_inc(v_maxHeartbeats_220_);
lean_inc(v_initHeartbeats_219_);
lean_inc(v_openDecls_218_);
lean_inc(v_currNamespace_217_);
lean_inc(v_maxRecDepth_215_);
lean_inc(v_currRecDepth_214_);
lean_inc_ref(v_options_213_);
lean_inc_ref(v_fileMap_212_);
lean_inc_ref(v_fileName_211_);
v___x_228_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_228_, 0, v_fileName_211_);
lean_ctor_set(v___x_228_, 1, v_fileMap_212_);
lean_ctor_set(v___x_228_, 2, v_options_213_);
lean_ctor_set(v___x_228_, 3, v_currRecDepth_214_);
lean_ctor_set(v___x_228_, 4, v_maxRecDepth_215_);
lean_ctor_set(v___x_228_, 5, v_ref_227_);
lean_ctor_set(v___x_228_, 6, v_currNamespace_217_);
lean_ctor_set(v___x_228_, 7, v_openDecls_218_);
lean_ctor_set(v___x_228_, 8, v_initHeartbeats_219_);
lean_ctor_set(v___x_228_, 9, v_maxHeartbeats_220_);
lean_ctor_set(v___x_228_, 10, v_quotContext_221_);
lean_ctor_set(v___x_228_, 11, v_currMacroScope_222_);
lean_ctor_set(v___x_228_, 12, v_cancelTk_x3f_224_);
lean_ctor_set(v___x_228_, 13, v_inheritedTraceOptions_226_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*14, v_diag_223_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*14 + 1, v_suppressElabErrors_225_);
v___x_229_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___x_228_, v___y_209_);
lean_dec_ref(v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg___boxed(lean_object* v_ref_230_, lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_ref_230_, v_msg_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v_ref_230_);
return v_res_239_;
}
}
static lean_object* _init_l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__5));
v___x_252_ = l_Lean_stringToMessageData(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(uint8_t v_firstChoiceOnly_253_, lean_object* v_stx_254_, lean_object* v_b_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_b_264_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v_a_295_; uint8_t v___x_322_; 
v___x_322_ = l_Lean_Syntax_isAntiquot(v_stx_254_);
if (v___x_322_ == 0)
{
uint8_t v___x_323_; 
lean_inc(v_stx_254_);
v___x_323_ = l_Lean_Syntax_isTokenAntiquot(v_stx_254_);
if (v___x_323_ == 0)
{
v_a_295_ = v_b_255_;
goto v___jp_294_;
}
else
{
goto v___jp_305_;
}
}
else
{
goto v___jp_305_;
}
v___jp_263_:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_b_264_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
v___jp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; size_t v_sz_272_; size_t v___x_273_; lean_object* v___x_274_; 
v___x_270_ = lean_box(0);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___y_268_);
v_sz_272_ = lean_array_size(v___y_269_);
v___x_273_ = ((size_t)0ULL);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(v_firstChoiceOnly_253_, v___y_269_, v_sz_272_, v___x_273_, v___x_271_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec_ref(v___y_269_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_285_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_285_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_285_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_285_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v_fst_279_; 
v_fst_279_ = lean_ctor_get(v_a_275_, 0);
if (lean_obj_tag(v_fst_279_) == 0)
{
lean_object* v_snd_280_; 
lean_del_object(v___x_277_);
v_snd_280_ = lean_ctor_get(v_a_275_, 1);
lean_inc(v_snd_280_);
lean_dec(v_a_275_);
v_b_264_ = v_snd_280_;
goto v___jp_263_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_283_; 
lean_inc_ref(v_fst_279_);
lean_dec(v_a_275_);
v_val_281_ = lean_ctor_get(v_fst_279_, 0);
lean_inc(v_val_281_);
lean_dec_ref(v_fst_279_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v_val_281_);
v___x_283_ = v___x_277_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_val_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_a_286_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_274_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_274_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
v___jp_294_:
{
if (lean_obj_tag(v_stx_254_) == 1)
{
if (v_firstChoiceOnly_253_ == 0)
{
lean_object* v_args_296_; 
v_args_296_ = lean_ctor_get(v_stx_254_, 2);
lean_inc_ref(v_args_296_);
lean_dec_ref(v_stx_254_);
v___y_268_ = v_a_295_;
v___y_269_ = v_args_296_;
goto v___jp_267_;
}
else
{
lean_object* v_kind_297_; lean_object* v_args_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_kind_297_ = lean_ctor_get(v_stx_254_, 1);
lean_inc(v_kind_297_);
v_args_298_ = lean_ctor_get(v_stx_254_, 2);
lean_inc_ref(v_args_298_);
lean_dec_ref(v_stx_254_);
v___x_299_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1));
v___x_300_ = lean_name_eq(v_kind_297_, v___x_299_);
lean_dec(v_kind_297_);
if (v___x_300_ == 0)
{
v___y_268_ = v_a_295_;
v___y_269_ = v_args_298_;
goto v___jp_267_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_box(0);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_array_get(v___x_301_, v_args_298_, v___x_302_);
lean_dec_ref(v_args_298_);
v_stx_254_ = v___x_303_;
v_b_255_ = v_a_295_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_254_);
v_b_264_ = v_a_295_;
goto v___jp_263_;
}
}
v___jp_305_:
{
uint8_t v___x_306_; 
v___x_306_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_254_);
if (v___x_306_ == 0)
{
lean_object* v_anti_307_; uint8_t v___x_308_; 
v_anti_307_ = l_Lean_Syntax_getAntiquotTerm(v_stx_254_);
v___x_308_ = l_Lean_Syntax_isIdent(v_anti_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4));
v___x_310_ = l_Lean_Syntax_isOfKind(v_anti_307_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_obj_once(&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6, &l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6_once, _init_l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6);
v___x_312_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_254_, v___x_311_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_dec_ref(v___x_312_);
v_a_295_ = v_b_255_;
goto v___jp_294_;
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref(v_b_255_);
lean_dec(v_stx_254_);
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
else
{
v_a_295_ = v_b_255_;
goto v___jp_294_;
}
}
else
{
lean_object* v_ids_321_; 
v_ids_321_ = lean_array_push(v_b_255_, v_anti_307_);
v_a_295_ = v_ids_321_;
goto v___jp_294_;
}
}
else
{
v_a_295_ = v_b_255_;
goto v___jp_294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(uint8_t v_firstChoiceOnly_324_, lean_object* v_as_325_, size_t v_sz_326_, size_t v_i_327_, lean_object* v_b_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = lean_usize_dec_lt(v_i_327_, v_sz_326_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v_b_328_);
return v___x_337_;
}
else
{
lean_object* v_snd_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_372_; 
v_snd_338_ = lean_ctor_get(v_b_328_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_b_328_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v_b_328_, 0);
lean_dec(v_unused_373_);
v___x_340_ = v_b_328_;
v_isShared_341_ = v_isSharedCheck_372_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_snd_338_);
lean_dec(v_b_328_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_372_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_a_342_; lean_object* v___x_343_; 
v_a_342_ = lean_array_uget_borrowed(v_as_325_, v_i_327_);
lean_inc(v_snd_338_);
lean_inc(v_a_342_);
v___x_343_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_324_, v_a_342_, v_snd_338_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_363_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_363_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_363_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_363_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
if (lean_obj_tag(v_a_344_) == 0)
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v_a_344_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_348_);
v___x_350_ = v___x_340_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_snd_338_);
v___x_350_ = v_reuseFailAlloc_354_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_352_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_350_);
v___x_352_ = v___x_346_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
lean_del_object(v___x_346_);
lean_dec(v_snd_338_);
v_a_355_ = lean_ctor_get(v_a_344_, 0);
lean_inc(v_a_355_);
lean_dec_ref(v_a_344_);
v___x_356_ = lean_box(0);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v_a_355_);
lean_ctor_set(v___x_340_, 0, v___x_356_);
v___x_358_ = v___x_340_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_a_355_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
size_t v___x_359_; size_t v___x_360_; 
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_add(v_i_327_, v___x_359_);
v_i_327_ = v___x_360_;
v_b_328_ = v___x_358_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_del_object(v___x_340_);
lean_dec(v_snd_338_);
v_a_364_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_343_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_343_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2___boxed(lean_object* v_firstChoiceOnly_374_, lean_object* v_as_375_, lean_object* v_sz_376_, lean_object* v_i_377_, lean_object* v_b_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_386_; size_t v_sz_boxed_387_; size_t v_i_boxed_388_; lean_object* v_res_389_; 
v_firstChoiceOnly_boxed_386_ = lean_unbox(v_firstChoiceOnly_374_);
v_sz_boxed_387_ = lean_unbox_usize(v_sz_376_);
lean_dec(v_sz_376_);
v_i_boxed_388_ = lean_unbox_usize(v_i_377_);
lean_dec(v_i_377_);
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(v_firstChoiceOnly_boxed_386_, v_as_375_, v_sz_boxed_387_, v_i_boxed_388_, v_b_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec_ref(v_as_375_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___boxed(lean_object* v_firstChoiceOnly_390_, lean_object* v_stx_391_, lean_object* v_b_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_400_; lean_object* v_res_401_; 
v_firstChoiceOnly_boxed_400_ = lean_unbox(v_firstChoiceOnly_390_);
v_res_401_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_boxed_400_, v_stx_391_, v_b_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds(lean_object* v_stx_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
uint8_t v___x_412_; lean_object* v___x_413_; uint8_t v_firstChoiceOnly_414_; lean_object* v_stx_415_; lean_object* v_ids_416_; lean_object* v___x_417_; 
v___x_412_ = 1;
v___x_413_ = l_Lean_Syntax_topDown(v_stx_404_, v___x_412_);
v_firstChoiceOnly_414_ = lean_ctor_get_uint8(v___x_413_, sizeof(void*)*1);
v_stx_415_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_stx_415_);
lean_dec_ref(v___x_413_);
v_ids_416_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_417_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_414_, v_stx_415_, v_ids_416_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_426_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_a_422_; lean_object* v___x_424_; 
v_a_422_ = lean_ctor_get(v_a_418_, 0);
lean_inc(v_a_422_);
lean_dec(v_a_418_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v_a_422_);
v___x_424_ = v___x_420_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_a_427_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_417_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_417_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds___boxed(lean_object* v_stx_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds(v_stx_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(lean_object* v_00_u03b1_444_, lean_object* v_ref_445_, lean_object* v_msg_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_ref_445_, v_msg_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___boxed(lean_object* v_00_u03b1_455_, lean_object* v_ref_456_, lean_object* v_msg_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(v_00_u03b1_455_, v_ref_456_, v_msg_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v_ref_456_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(lean_object* v_00_u03b1_466_, lean_object* v_msg_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___boxed(lean_object* v_00_u03b1_476_, lean_object* v_msg_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(v_00_u03b1_476_, v_msg_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(lean_object* v_msgData_486_, lean_object* v_macroStack_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_msgData_486_, v_macroStack_487_, v___y_492_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_496_, lean_object* v_macroStack_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(v_msgData_496_, v_macroStack_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_505_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__4));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternVars(lean_object* v_stx_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Syntax_isQuot(v_stx_518_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4));
lean_inc(v_stx_518_);
v___x_528_ = l_Lean_Syntax_isOfKind(v_stx_518_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__1));
lean_inc(v_stx_518_);
v___x_530_ = l_Lean_Syntax_isOfKind(v_stx_518_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__3));
lean_inc(v_stx_518_);
v___x_532_ = l_Lean_Syntax_isOfKind(v_stx_518_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_533_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_518_);
v___x_534_ = l_Lean_MessageData_ofSyntax(v_stx_518_);
v___x_535_ = l_Lean_indentD(v___x_534_);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_518_, v___x_536_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_stx_518_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = l_Lean_Syntax_getArg(v_stx_518_, v___x_538_);
lean_inc(v___x_539_);
v___x_540_ = l_Lean_Syntax_isOfKind(v___x_539_, v___x_529_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v___x_539_);
v___x_541_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_518_);
v___x_542_ = l_Lean_MessageData_ofSyntax(v_stx_518_);
v___x_543_ = l_Lean_indentD(v___x_542_);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_541_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_518_, v___x_544_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_stx_518_);
return v___x_545_;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_546_ = lean_unsigned_to_nat(2u);
v___x_547_ = l_Lean_Syntax_getArg(v_stx_518_, v___x_546_);
v___x_548_ = l_Lean_Syntax_matchesNull(v___x_547_, v___x_538_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v___x_539_);
v___x_549_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_518_);
v___x_550_ = l_Lean_MessageData_ofSyntax(v_stx_518_);
v___x_551_ = l_Lean_indentD(v___x_550_);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_549_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_518_, v___x_552_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_stx_518_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(3u);
v___x_555_ = l_Lean_Syntax_getArg(v_stx_518_, v___x_554_);
lean_dec(v_stx_518_);
v___x_556_ = l_Lean_Elab_Term_Quotation_getPatternVars(v___x_555_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_565_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_565_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_array_push(v_a_557_, v___x_539_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
else
{
lean_dec(v___x_539_);
return v___x_556_;
}
}
}
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_mk_empty_array_with_capacity(v___x_566_);
v___x_568_ = lean_array_push(v___x_567_, v_stx_518_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_stx_518_);
v___x_570_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
else
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds(v_stx_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_581_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_572_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_572_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___boxed(lean_object* v_stx_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Elab_Term_Quotation_getPatternVars(v_stx_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(lean_object* v_as_598_, size_t v_i_599_, size_t v_stop_600_, lean_object* v_b_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_a_610_; uint8_t v___x_614_; 
v___x_614_ = lean_usize_dec_eq(v_i_599_, v_stop_600_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_array_uget_borrowed(v_as_598_, v_i_599_);
lean_inc(v___x_615_);
v___x_616_ = l_Lean_Elab_Term_Quotation_getPatternVars(v___x_615_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref(v___x_616_);
v___x_618_ = l_Array_append___redArg(v_b_601_, v_a_617_);
lean_dec(v_a_617_);
v_a_610_ = v___x_618_;
goto v___jp_609_;
}
else
{
lean_dec_ref(v_b_601_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_619_; 
v_a_619_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v___x_616_);
v_a_610_ = v_a_619_;
goto v___jp_609_;
}
else
{
return v___x_616_;
}
}
}
else
{
lean_object* v___x_620_; 
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v_b_601_);
return v___x_620_;
}
v___jp_609_:
{
size_t v___x_611_; size_t v___x_612_; 
v___x_611_ = ((size_t)1ULL);
v___x_612_ = lean_usize_add(v_i_599_, v___x_611_);
v_i_599_ = v___x_612_;
v_b_601_ = v_a_610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0___boxed(lean_object* v_as_621_, lean_object* v_i_622_, lean_object* v_stop_623_, lean_object* v_b_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
size_t v_i_boxed_632_; size_t v_stop_boxed_633_; lean_object* v_res_634_; 
v_i_boxed_632_ = lean_unbox_usize(v_i_622_);
lean_dec(v_i_622_);
v_stop_boxed_633_ = lean_unbox_usize(v_stop_623_);
lean_dec(v_stop_623_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_as_621_, v_i_boxed_632_, v_stop_boxed_633_, v_b_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec_ref(v_as_621_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars(lean_object* v_pats_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_645_ = lean_array_get_size(v_pats_635_);
v___x_646_ = lean_nat_dec_lt(v___x_643_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_644_);
return v___x_647_;
}
else
{
uint8_t v___x_648_; 
v___x_648_ = lean_nat_dec_le(v___x_645_, v___x_645_);
if (v___x_648_ == 0)
{
if (v___x_646_ == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_644_);
return v___x_649_;
}
else
{
size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
v___x_650_ = ((size_t)0ULL);
v___x_651_ = lean_usize_of_nat(v___x_645_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_pats_635_, v___x_650_, v___x_651_, v___x_644_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_652_;
}
}
else
{
size_t v___x_653_; size_t v___x_654_; lean_object* v___x_655_; 
v___x_653_ = ((size_t)0ULL);
v___x_654_ = lean_usize_of_nat(v___x_645_);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_pats_635_, v___x_653_, v___x_654_, v___x_644_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars___boxed(lean_object* v_pats_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Elab_Term_Quotation_getPatternsVars(v_pats_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec_ref(v_pats_656_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(lean_object* v_antiquot_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_name_669_; uint8_t v___x_670_; 
v___x_666_ = lean_unsigned_to_nat(3u);
v___x_667_ = l_Lean_Syntax_getArg(v_antiquot_665_, v___x_666_);
v___x_668_ = lean_unsigned_to_nat(1u);
v_name_669_ = l_Lean_Syntax_getArg(v___x_667_, v___x_668_);
lean_dec(v___x_667_);
v___x_670_ = l_Lean_Syntax_isMissing(v_name_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v_name_669_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; 
lean_dec(v_name_669_);
v___x_672_ = lean_box(0);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f___boxed(lean_object* v_antiquot_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(v_antiquot_673_);
lean_dec(v_antiquot_673_);
return v_res_674_;
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
