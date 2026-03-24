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
lean_inc_ref(v___y_204_);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(uint8_t v_firstChoiceOnly_253_, lean_object* v_stx_254_, lean_object* v_b_255_, lean_object* v_inst_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_b_265_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v_a_296_; uint8_t v___x_323_; 
v___x_323_ = l_Lean_Syntax_isAntiquot(v_stx_254_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; 
lean_inc(v_stx_254_);
v___x_324_ = l_Lean_Syntax_isTokenAntiquot(v_stx_254_);
if (v___x_324_ == 0)
{
v_a_296_ = v_b_255_;
goto v___jp_295_;
}
else
{
goto v___jp_306_;
}
}
else
{
goto v___jp_306_;
}
v___jp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v_b_265_);
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
v___jp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; size_t v_sz_273_; size_t v___x_274_; lean_object* v___x_275_; 
v___x_271_ = lean_box(0);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___y_269_);
v_sz_273_ = lean_array_size(v___y_270_);
v___x_274_ = ((size_t)0ULL);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(v_firstChoiceOnly_253_, v_inst_256_, v___y_270_, v_sz_273_, v___x_274_, v___x_272_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec_ref(v___y_270_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_286_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_286_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_fst_280_; 
v_fst_280_ = lean_ctor_get(v_a_276_, 0);
if (lean_obj_tag(v_fst_280_) == 0)
{
lean_object* v_snd_281_; 
lean_del_object(v___x_278_);
v_snd_281_ = lean_ctor_get(v_a_276_, 1);
lean_inc(v_snd_281_);
lean_dec(v_a_276_);
v_b_265_ = v_snd_281_;
goto v___jp_264_;
}
else
{
lean_object* v_val_282_; lean_object* v___x_284_; 
lean_inc_ref(v_fst_280_);
lean_dec(v_a_276_);
v_val_282_ = lean_ctor_get(v_fst_280_, 0);
lean_inc(v_val_282_);
lean_dec_ref(v_fst_280_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v_val_282_);
v___x_284_ = v___x_278_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_val_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_a_287_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_275_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_275_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
v___jp_295_:
{
if (lean_obj_tag(v_stx_254_) == 1)
{
if (v_firstChoiceOnly_253_ == 0)
{
lean_object* v_args_297_; 
v_args_297_ = lean_ctor_get(v_stx_254_, 2);
lean_inc_ref(v_args_297_);
lean_dec_ref(v_stx_254_);
v___y_269_ = v_a_296_;
v___y_270_ = v_args_297_;
goto v___jp_268_;
}
else
{
lean_object* v_kind_298_; lean_object* v_args_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_kind_298_ = lean_ctor_get(v_stx_254_, 1);
lean_inc(v_kind_298_);
v_args_299_ = lean_ctor_get(v_stx_254_, 2);
lean_inc_ref(v_args_299_);
lean_dec_ref(v_stx_254_);
v___x_300_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1));
v___x_301_ = lean_name_eq(v_kind_298_, v___x_300_);
lean_dec(v_kind_298_);
if (v___x_301_ == 0)
{
v___y_269_ = v_a_296_;
v___y_270_ = v_args_299_;
goto v___jp_268_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_box(0);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_array_get(v___x_302_, v_args_299_, v___x_303_);
lean_dec_ref(v_args_299_);
v_stx_254_ = v___x_304_;
v_b_255_ = v_a_296_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_254_);
v_b_265_ = v_a_296_;
goto v___jp_264_;
}
}
v___jp_306_:
{
uint8_t v___x_307_; 
v___x_307_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_254_);
if (v___x_307_ == 0)
{
lean_object* v_anti_308_; uint8_t v___x_309_; 
v_anti_308_ = l_Lean_Syntax_getAntiquotTerm(v_stx_254_);
v___x_309_ = l_Lean_Syntax_isIdent(v_anti_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4));
v___x_311_ = l_Lean_Syntax_isOfKind(v_anti_308_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_obj_once(&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6, &l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6_once, _init_l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6);
v___x_313_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_254_, v___x_312_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_dec_ref(v___x_313_);
v_a_296_ = v_b_255_;
goto v___jp_295_;
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v_b_255_);
lean_dec(v_stx_254_);
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
v_a_296_ = v_b_255_;
goto v___jp_295_;
}
}
else
{
lean_object* v_ids_322_; 
v_ids_322_ = lean_array_push(v_b_255_, v_anti_308_);
v_a_296_ = v_ids_322_;
goto v___jp_295_;
}
}
else
{
v_a_296_ = v_b_255_;
goto v___jp_295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(uint8_t v_firstChoiceOnly_325_, lean_object* v_inst_326_, lean_object* v_as_327_, size_t v_sz_328_, size_t v_i_329_, lean_object* v_b_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_usize_dec_lt(v_i_329_, v_sz_328_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v_b_330_);
return v___x_339_;
}
else
{
lean_object* v_snd_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_374_; 
v_snd_340_ = lean_ctor_get(v_b_330_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_b_330_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v_b_330_, 0);
lean_dec(v_unused_375_);
v___x_342_ = v_b_330_;
v_isShared_343_ = v_isSharedCheck_374_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_snd_340_);
lean_dec(v_b_330_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_374_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v_a_344_; lean_object* v___x_345_; 
v_a_344_ = lean_array_uget_borrowed(v_as_327_, v_i_329_);
lean_inc(v_snd_340_);
lean_inc(v_a_344_);
v___x_345_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_325_, v_a_344_, v_snd_340_, v_inst_326_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_365_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_365_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_365_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_365_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
if (lean_obj_tag(v_a_346_) == 0)
{
lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_a_346_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_350_);
v___x_352_ = v___x_342_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_snd_340_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_354_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_352_);
v___x_354_ = v___x_348_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
lean_del_object(v___x_348_);
lean_dec(v_snd_340_);
v_a_357_ = lean_ctor_get(v_a_346_, 0);
lean_inc(v_a_357_);
lean_dec_ref(v_a_346_);
v___x_358_ = lean_box(0);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 1, v_a_357_);
lean_ctor_set(v___x_342_, 0, v___x_358_);
v___x_360_ = v___x_342_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_a_357_);
v___x_360_ = v_reuseFailAlloc_364_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
size_t v___x_361_; size_t v___x_362_; 
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_add(v_i_329_, v___x_361_);
v_i_329_ = v___x_362_;
v_b_330_ = v___x_360_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
lean_del_object(v___x_342_);
lean_dec(v_snd_340_);
v_a_366_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v___x_345_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_345_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_366_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2___boxed(lean_object* v_firstChoiceOnly_376_, lean_object* v_inst_377_, lean_object* v_as_378_, lean_object* v_sz_379_, lean_object* v_i_380_, lean_object* v_b_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_389_; size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_firstChoiceOnly_boxed_389_ = lean_unbox(v_firstChoiceOnly_376_);
v_sz_boxed_390_ = lean_unbox_usize(v_sz_379_);
lean_dec(v_sz_379_);
v_i_boxed_391_ = lean_unbox_usize(v_i_380_);
lean_dec(v_i_380_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(v_firstChoiceOnly_boxed_389_, v_inst_377_, v_as_378_, v_sz_boxed_390_, v_i_boxed_391_, v_b_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec_ref(v_as_378_);
lean_dec_ref(v_inst_377_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___boxed(lean_object* v_firstChoiceOnly_393_, lean_object* v_stx_394_, lean_object* v_b_395_, lean_object* v_inst_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_404_; lean_object* v_res_405_; 
v_firstChoiceOnly_boxed_404_ = lean_unbox(v_firstChoiceOnly_393_);
v_res_405_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_boxed_404_, v_stx_394_, v_b_395_, v_inst_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec_ref(v_inst_396_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds(lean_object* v_stx_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
uint8_t v___x_416_; lean_object* v___x_417_; uint8_t v_firstChoiceOnly_418_; lean_object* v_stx_419_; lean_object* v_ids_420_; lean_object* v___x_421_; 
v___x_416_ = 1;
v___x_417_ = l_Lean_Syntax_topDown(v_stx_408_, v___x_416_);
v_firstChoiceOnly_418_ = lean_ctor_get_uint8(v___x_417_, sizeof(void*)*1);
v_stx_419_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_stx_419_);
lean_dec_ref(v___x_417_);
v_ids_420_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_421_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_418_, v_stx_419_, v_ids_420_, v_ids_420_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_430_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_430_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_a_426_; lean_object* v___x_428_; 
v_a_426_ = lean_ctor_get(v_a_422_, 0);
lean_inc(v_a_426_);
lean_dec(v_a_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v_a_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_a_431_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_421_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_421_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds___boxed(lean_object* v_stx_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds(v_stx_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(lean_object* v_00_u03b1_448_, lean_object* v_ref_449_, lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_ref_449_, v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___boxed(lean_object* v_00_u03b1_459_, lean_object* v_ref_460_, lean_object* v_msg_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(v_00_u03b1_459_, v_ref_460_, v_msg_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v_ref_460_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(lean_object* v_00_u03b1_470_, lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; 
lean_inc_ref(v___y_472_);
v___x_479_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___boxed(lean_object* v_00_u03b1_480_, lean_object* v_msg_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(v_00_u03b1_480_, v_msg_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(lean_object* v_msgData_490_, lean_object* v_macroStack_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_msgData_490_, v_macroStack_491_, v___y_496_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_500_, lean_object* v_macroStack_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(v_msgData_500_, v_macroStack_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__4));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternVars(lean_object* v_stx_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = l_Lean_Syntax_isQuot(v_stx_522_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4));
lean_inc(v_stx_522_);
v___x_532_ = l_Lean_Syntax_isOfKind(v_stx_522_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__1));
lean_inc(v_stx_522_);
v___x_534_ = l_Lean_Syntax_isOfKind(v_stx_522_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__3));
lean_inc(v_stx_522_);
v___x_536_ = l_Lean_Syntax_isOfKind(v_stx_522_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_537_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_522_);
v___x_538_ = l_Lean_MessageData_ofSyntax(v_stx_522_);
v___x_539_ = l_Lean_indentD(v___x_538_);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_537_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_522_, v___x_540_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_stx_522_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = l_Lean_Syntax_getArg(v_stx_522_, v___x_542_);
lean_inc(v___x_543_);
v___x_544_ = l_Lean_Syntax_isOfKind(v___x_543_, v___x_533_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v___x_543_);
v___x_545_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_522_);
v___x_546_ = l_Lean_MessageData_ofSyntax(v_stx_522_);
v___x_547_ = l_Lean_indentD(v___x_546_);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_545_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_522_, v___x_548_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_stx_522_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = l_Lean_Syntax_getArg(v_stx_522_, v___x_550_);
v___x_552_ = l_Lean_Syntax_matchesNull(v___x_551_, v___x_542_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec(v___x_543_);
v___x_553_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_522_);
v___x_554_ = l_Lean_MessageData_ofSyntax(v_stx_522_);
v___x_555_ = l_Lean_indentD(v___x_554_);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_553_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_522_, v___x_556_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_stx_522_);
return v___x_557_;
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_unsigned_to_nat(3u);
v___x_559_ = l_Lean_Syntax_getArg(v_stx_522_, v___x_558_);
lean_dec(v_stx_522_);
v___x_560_ = l_Lean_Elab_Term_Quotation_getPatternVars(v___x_559_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_569_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_569_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = lean_array_push(v_a_561_, v___x_543_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
else
{
lean_dec(v___x_543_);
return v___x_560_;
}
}
}
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_mk_empty_array_with_capacity(v___x_570_);
v___x_572_ = lean_array_push(v___x_571_, v_stx_522_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v_stx_522_);
v___x_574_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
else
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds(v_stx_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
v_a_585_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_576_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_576_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___boxed(lean_object* v_stx_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Elab_Term_Quotation_getPatternVars(v_stx_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(lean_object* v_as_602_, size_t v_i_603_, size_t v_stop_604_, lean_object* v_b_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_a_614_; uint8_t v___x_618_; 
v___x_618_ = lean_usize_dec_eq(v_i_603_, v_stop_604_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_array_uget_borrowed(v_as_602_, v_i_603_);
lean_inc(v___x_619_);
v___x_620_ = l_Lean_Elab_Term_Quotation_getPatternVars(v___x_619_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref(v___x_620_);
v___x_622_ = l_Array_append___redArg(v_b_605_, v_a_621_);
lean_dec(v_a_621_);
v_a_614_ = v___x_622_;
goto v___jp_613_;
}
else
{
lean_dec_ref(v_b_605_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_623_; 
v_a_623_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_623_);
lean_dec_ref(v___x_620_);
v_a_614_ = v_a_623_;
goto v___jp_613_;
}
else
{
return v___x_620_;
}
}
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_b_605_);
return v___x_624_;
}
v___jp_613_:
{
size_t v___x_615_; size_t v___x_616_; 
v___x_615_ = ((size_t)1ULL);
v___x_616_ = lean_usize_add(v_i_603_, v___x_615_);
v_i_603_ = v___x_616_;
v_b_605_ = v_a_614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0___boxed(lean_object* v_as_625_, lean_object* v_i_626_, lean_object* v_stop_627_, lean_object* v_b_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
size_t v_i_boxed_636_; size_t v_stop_boxed_637_; lean_object* v_res_638_; 
v_i_boxed_636_ = lean_unbox_usize(v_i_626_);
lean_dec(v_i_626_);
v_stop_boxed_637_ = lean_unbox_usize(v_stop_627_);
lean_dec(v_stop_627_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_as_625_, v_i_boxed_636_, v_stop_boxed_637_, v_b_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec_ref(v_as_625_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars(lean_object* v_pats_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_649_ = lean_array_get_size(v_pats_639_);
v___x_650_ = lean_nat_dec_lt(v___x_647_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_648_);
return v___x_651_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_le(v___x_649_, v___x_649_);
if (v___x_652_ == 0)
{
if (v___x_650_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_648_);
return v___x_653_;
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
v___x_654_ = ((size_t)0ULL);
v___x_655_ = lean_usize_of_nat(v___x_649_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_pats_639_, v___x_654_, v___x_655_, v___x_648_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
return v___x_656_;
}
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = ((size_t)0ULL);
v___x_658_ = lean_usize_of_nat(v___x_649_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_pats_639_, v___x_657_, v___x_658_, v___x_648_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars___boxed(lean_object* v_pats_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Elab_Term_Quotation_getPatternsVars(v_pats_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec_ref(v_pats_660_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(lean_object* v_antiquot_669_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_name_673_; uint8_t v___x_674_; 
v___x_670_ = lean_unsigned_to_nat(3u);
v___x_671_ = l_Lean_Syntax_getArg(v_antiquot_669_, v___x_670_);
v___x_672_ = lean_unsigned_to_nat(1u);
v_name_673_ = l_Lean_Syntax_getArg(v___x_671_, v___x_672_);
lean_dec(v___x_671_);
v___x_674_ = l_Lean_Syntax_isMissing(v_name_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v_name_673_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; 
lean_dec(v_name_673_);
v___x_676_ = lean_box(0);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f___boxed(lean_object* v_antiquot_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(v_antiquot_677_);
lean_dec(v_antiquot_677_);
return v_res_678_;
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
