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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hygiene"};
static const lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(187, 171, 26, 124, 58, 231, 48, 110)}};
static const lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 243, .m_capacity = 243, .m_length = 242, .m_data = "Annotate identifiers in quotations such that they are resolved relative to the scope at their declaration, not that at their eventual use/expansion, to avoid accidental capturing. Note that quotations/notations already defined are unaffected."};
static const lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Quotation"};
static const lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(66, 249, 245, 72, 137, 60, 151, 235)}};
static const lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
static const lean_ctor_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_0),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_Quotation_getPatternVars___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4____boxed(lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1(lean_object* v_msgData_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; lean_object* v_env_67_; lean_object* v___x_68_; lean_object* v_mctx_69_; lean_object* v_lctx_70_; lean_object* v_options_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_66_ = lean_st_ref_get(v___y_64_);
v_env_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc_ref(v_env_67_);
lean_dec(v___x_66_);
v___x_68_ = lean_st_ref_get(v___y_62_);
v_mctx_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_mctx_69_);
lean_dec(v___x_68_);
v_lctx_70_ = lean_ctor_get(v___y_61_, 2);
v_options_71_ = lean_ctor_get(v___y_63_, 2);
lean_inc_ref(v_options_71_);
lean_inc_ref(v_lctx_70_);
v___x_72_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_72_, 0, v_env_67_);
lean_ctor_set(v___x_72_, 1, v_mctx_69_);
lean_ctor_set(v___x_72_, 2, v_lctx_70_);
lean_ctor_set(v___x_72_, 3, v_options_71_);
v___x_73_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v_msgData_60_);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1(v_msgData_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_81_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4(lean_object* v_opts_82_, lean_object* v_opt_83_){
_start:
{
lean_object* v_name_84_; lean_object* v_defValue_85_; lean_object* v_map_86_; lean_object* v___x_87_; 
v_name_84_ = lean_ctor_get(v_opt_83_, 0);
v_defValue_85_ = lean_ctor_get(v_opt_83_, 1);
v_map_86_ = lean_ctor_get(v_opts_82_, 0);
v___x_87_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_86_, v_name_84_);
if (lean_obj_tag(v___x_87_) == 0)
{
uint8_t v___x_88_; 
v___x_88_ = lean_unbox(v_defValue_85_);
return v___x_88_;
}
else
{
lean_object* v_val_89_; 
v_val_89_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_val_89_);
lean_dec_ref(v___x_87_);
if (lean_obj_tag(v_val_89_) == 1)
{
uint8_t v_v_90_; 
v_v_90_ = lean_ctor_get_uint8(v_val_89_, 0);
lean_dec_ref(v_val_89_);
return v_v_90_;
}
else
{
uint8_t v___x_91_; 
lean_dec(v_val_89_);
v___x_91_ = lean_unbox(v_defValue_85_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_opts_92_, lean_object* v_opt_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4(v_opts_92_, v_opt_93_);
lean_dec_ref(v_opt_93_);
lean_dec_ref(v_opts_92_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_box(1);
v___x_97_ = l_Lean_MessageData_ofFormat(v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__2));
v___x_102_ = l_Lean_MessageData_ofFormat(v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
return v_x_103_;
}
else
{
lean_object* v_head_105_; lean_object* v_tail_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_128_; 
v_head_105_ = lean_ctor_get(v_x_104_, 0);
v_tail_106_ = lean_ctor_get(v_x_104_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_128_ == 0)
{
v___x_108_ = v_x_104_;
v_isShared_109_ = v_isSharedCheck_128_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_tail_106_);
lean_inc(v_head_105_);
lean_dec(v_x_104_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_128_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v_before_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_126_; 
v_before_110_ = lean_ctor_get(v_head_105_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v_head_105_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v_head_105_, 1);
lean_dec(v_unused_127_);
v___x_112_ = v_head_105_;
v_isShared_113_ = v_isSharedCheck_126_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_before_110_);
lean_dec(v_head_105_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_126_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 7);
lean_ctor_set(v___x_112_, 1, v___x_114_);
lean_ctor_set(v___x_112_, 0, v_x_103_);
v___x_116_ = v___x_112_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_x_103_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_114_);
v___x_116_ = v_reuseFailAlloc_125_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_117_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__3);
if (v_isShared_109_ == 0)
{
lean_ctor_set_tag(v___x_108_, 7);
lean_ctor_set(v___x_108_, 1, v___x_117_);
lean_ctor_set(v___x_108_, 0, v___x_116_);
v___x_119_ = v___x_108_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_117_);
v___x_119_ = v_reuseFailAlloc_124_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = l_Lean_MessageData_ofSyntax(v_before_110_);
v___x_121_ = l_Lean_indentD(v___x_120_);
v___x_122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_119_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v_x_103_ = v___x_122_;
v_x_104_ = v_tail_106_;
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
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_133_ = l_Lean_MessageData_ofFormat(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(lean_object* v_msgData_134_, lean_object* v_macroStack_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_options_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_options_138_ = lean_ctor_get(v___y_136_, 2);
v___x_139_ = l_Lean_Elab_pp_macroStack;
v___x_140_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__4(v_options_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
lean_dec(v_macroStack_135_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v_msgData_134_);
return v___x_141_;
}
else
{
if (lean_obj_tag(v_macroStack_135_) == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v_msgData_134_);
return v___x_142_;
}
else
{
lean_object* v_head_143_; lean_object* v_after_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_159_; 
v_head_143_ = lean_ctor_get(v_macroStack_135_, 0);
lean_inc(v_head_143_);
v_after_144_ = lean_ctor_get(v_head_143_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_head_143_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_head_143_, 0);
lean_dec(v_unused_160_);
v___x_146_ = v_head_143_;
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_after_144_);
lean_dec(v_head_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_148_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5___closed__0);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 7);
lean_ctor_set(v___x_146_, 1, v___x_148_);
lean_ctor_set(v___x_146_, 0, v_msgData_134_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_msgData_134_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_148_);
v___x_150_ = v_reuseFailAlloc_158_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_msgData_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_151_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Lean_MessageData_ofSyntax(v_after_144_);
v___x_154_ = l_Lean_indentD(v___x_153_);
v_msgData_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_155_, 0, v___x_152_);
lean_ctor_set(v_msgData_155_, 1, v___x_154_);
v___x_156_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2_spec__5(v_msgData_155_, v_macroStack_135_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msgData_161_, lean_object* v_macroStack_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_msgData_161_, v_macroStack_162_, v___y_163_);
lean_dec_ref(v___y_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_ref_174_; lean_object* v___x_175_; lean_object* v_a_176_; lean_object* v_macroStack_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_188_; 
v_ref_174_ = lean_ctor_get(v___y_171_, 5);
v___x_175_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__1(v_msg_166_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref(v___x_175_);
v_macroStack_177_ = lean_ctor_get(v___y_167_, 1);
lean_inc_n(v_macroStack_177_, 2);
v___x_178_ = l_Lean_Elab_getBetterRef(v_ref_174_, v_macroStack_177_);
v___x_179_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_a_176_, v_macroStack_177_, v___y_171_);
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_188_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_178_);
lean_ctor_set(v___x_184_, 1, v_a_180_);
if (v_isShared_183_ == 0)
{
lean_ctor_set_tag(v___x_182_, 1);
lean_ctor_set(v___x_182_, 0, v___x_184_);
v___x_186_ = v___x_182_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg___boxed(lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(lean_object* v_ref_198_, lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_fileName_207_; lean_object* v_fileMap_208_; lean_object* v_options_209_; lean_object* v_currRecDepth_210_; lean_object* v_maxRecDepth_211_; lean_object* v_ref_212_; lean_object* v_currNamespace_213_; lean_object* v_openDecls_214_; lean_object* v_initHeartbeats_215_; lean_object* v_maxHeartbeats_216_; lean_object* v_quotContext_217_; lean_object* v_currMacroScope_218_; uint8_t v_diag_219_; lean_object* v_cancelTk_x3f_220_; uint8_t v_suppressElabErrors_221_; lean_object* v_inheritedTraceOptions_222_; lean_object* v_ref_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_fileName_207_ = lean_ctor_get(v___y_204_, 0);
v_fileMap_208_ = lean_ctor_get(v___y_204_, 1);
v_options_209_ = lean_ctor_get(v___y_204_, 2);
v_currRecDepth_210_ = lean_ctor_get(v___y_204_, 3);
v_maxRecDepth_211_ = lean_ctor_get(v___y_204_, 4);
v_ref_212_ = lean_ctor_get(v___y_204_, 5);
v_currNamespace_213_ = lean_ctor_get(v___y_204_, 6);
v_openDecls_214_ = lean_ctor_get(v___y_204_, 7);
v_initHeartbeats_215_ = lean_ctor_get(v___y_204_, 8);
v_maxHeartbeats_216_ = lean_ctor_get(v___y_204_, 9);
v_quotContext_217_ = lean_ctor_get(v___y_204_, 10);
v_currMacroScope_218_ = lean_ctor_get(v___y_204_, 11);
v_diag_219_ = lean_ctor_get_uint8(v___y_204_, sizeof(void*)*14);
v_cancelTk_x3f_220_ = lean_ctor_get(v___y_204_, 12);
v_suppressElabErrors_221_ = lean_ctor_get_uint8(v___y_204_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_222_ = lean_ctor_get(v___y_204_, 13);
v_ref_223_ = l_Lean_replaceRef(v_ref_198_, v_ref_212_);
lean_inc_ref(v_inheritedTraceOptions_222_);
lean_inc(v_cancelTk_x3f_220_);
lean_inc(v_currMacroScope_218_);
lean_inc(v_quotContext_217_);
lean_inc(v_maxHeartbeats_216_);
lean_inc(v_initHeartbeats_215_);
lean_inc(v_openDecls_214_);
lean_inc(v_currNamespace_213_);
lean_inc(v_maxRecDepth_211_);
lean_inc(v_currRecDepth_210_);
lean_inc_ref(v_options_209_);
lean_inc_ref(v_fileMap_208_);
lean_inc_ref(v_fileName_207_);
v___x_224_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_224_, 0, v_fileName_207_);
lean_ctor_set(v___x_224_, 1, v_fileMap_208_);
lean_ctor_set(v___x_224_, 2, v_options_209_);
lean_ctor_set(v___x_224_, 3, v_currRecDepth_210_);
lean_ctor_set(v___x_224_, 4, v_maxRecDepth_211_);
lean_ctor_set(v___x_224_, 5, v_ref_223_);
lean_ctor_set(v___x_224_, 6, v_currNamespace_213_);
lean_ctor_set(v___x_224_, 7, v_openDecls_214_);
lean_ctor_set(v___x_224_, 8, v_initHeartbeats_215_);
lean_ctor_set(v___x_224_, 9, v_maxHeartbeats_216_);
lean_ctor_set(v___x_224_, 10, v_quotContext_217_);
lean_ctor_set(v___x_224_, 11, v_currMacroScope_218_);
lean_ctor_set(v___x_224_, 12, v_cancelTk_x3f_220_);
lean_ctor_set(v___x_224_, 13, v_inheritedTraceOptions_222_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*14, v_diag_219_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*14 + 1, v_suppressElabErrors_221_);
v___x_225_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___x_224_, v___y_205_);
lean_dec_ref(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg___boxed(lean_object* v_ref_226_, lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_ref_226_, v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v_ref_226_);
return v_res_235_;
}
}
static lean_object* _init_l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__5));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(uint8_t v_firstChoiceOnly_249_, lean_object* v_stx_250_, lean_object* v_b_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_b_260_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v_a_291_; uint8_t v___x_318_; 
v___x_318_ = l_Lean_Syntax_isAntiquot(v_stx_250_);
if (v___x_318_ == 0)
{
uint8_t v___x_319_; 
lean_inc(v_stx_250_);
v___x_319_ = l_Lean_Syntax_isTokenAntiquot(v_stx_250_);
if (v___x_319_ == 0)
{
v_a_291_ = v_b_251_;
goto v___jp_290_;
}
else
{
goto v___jp_301_;
}
}
else
{
goto v___jp_301_;
}
v___jp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v_b_260_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
v___jp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; size_t v_sz_268_; size_t v___x_269_; lean_object* v___x_270_; 
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___y_265_);
v_sz_268_ = lean_array_size(v___y_264_);
v___x_269_ = ((size_t)0ULL);
v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(v_firstChoiceOnly_249_, v___y_264_, v_sz_268_, v___x_269_, v___x_267_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec_ref(v___y_264_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_281_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_281_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_281_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_281_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_fst_275_; 
v_fst_275_ = lean_ctor_get(v_a_271_, 0);
if (lean_obj_tag(v_fst_275_) == 0)
{
lean_object* v_snd_276_; 
lean_del_object(v___x_273_);
v_snd_276_ = lean_ctor_get(v_a_271_, 1);
lean_inc(v_snd_276_);
lean_dec(v_a_271_);
v_b_260_ = v_snd_276_;
goto v___jp_259_;
}
else
{
lean_object* v_val_277_; lean_object* v___x_279_; 
lean_inc_ref(v_fst_275_);
lean_dec(v_a_271_);
v_val_277_ = lean_ctor_get(v_fst_275_, 0);
lean_inc(v_val_277_);
lean_dec_ref(v_fst_275_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v_val_277_);
v___x_279_ = v___x_273_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_val_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_a_282_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_270_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_270_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
v___jp_290_:
{
if (lean_obj_tag(v_stx_250_) == 1)
{
if (v_firstChoiceOnly_249_ == 0)
{
lean_object* v_args_292_; 
v_args_292_ = lean_ctor_get(v_stx_250_, 2);
lean_inc_ref(v_args_292_);
lean_dec_ref(v_stx_250_);
v___y_264_ = v_args_292_;
v___y_265_ = v_a_291_;
goto v___jp_263_;
}
else
{
lean_object* v_kind_293_; lean_object* v_args_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_kind_293_ = lean_ctor_get(v_stx_250_, 1);
lean_inc(v_kind_293_);
v_args_294_ = lean_ctor_get(v_stx_250_, 2);
lean_inc_ref(v_args_294_);
lean_dec_ref(v_stx_250_);
v___x_295_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__1));
v___x_296_ = lean_name_eq(v_kind_293_, v___x_295_);
lean_dec(v_kind_293_);
if (v___x_296_ == 0)
{
v___y_264_ = v_args_294_;
v___y_265_ = v_a_291_;
goto v___jp_263_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_array_get(v___x_297_, v_args_294_, v___x_298_);
lean_dec_ref(v_args_294_);
v_stx_250_ = v___x_299_;
v_b_251_ = v_a_291_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_250_);
v_b_260_ = v_a_291_;
goto v___jp_259_;
}
}
v___jp_301_:
{
uint8_t v___x_302_; 
v___x_302_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_250_);
if (v___x_302_ == 0)
{
lean_object* v_anti_303_; uint8_t v___x_304_; 
v_anti_303_ = l_Lean_Syntax_getAntiquotTerm(v_stx_250_);
v___x_304_ = l_Lean_Syntax_isIdent(v_anti_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4));
v___x_306_ = l_Lean_Syntax_isOfKind(v_anti_303_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6, &l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6_once, _init_l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__6);
v___x_308_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_250_, v___x_307_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_dec_ref(v___x_308_);
v_a_291_ = v_b_251_;
goto v___jp_290_;
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v_b_251_);
lean_dec(v_stx_250_);
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
else
{
v_a_291_ = v_b_251_;
goto v___jp_290_;
}
}
else
{
lean_object* v_ids_317_; 
v_ids_317_ = lean_array_push(v_b_251_, v_anti_303_);
v_a_291_ = v_ids_317_;
goto v___jp_290_;
}
}
else
{
v_a_291_ = v_b_251_;
goto v___jp_290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(uint8_t v_firstChoiceOnly_320_, lean_object* v_as_321_, size_t v_sz_322_, size_t v_i_323_, lean_object* v_b_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
uint8_t v___x_332_; 
v___x_332_ = lean_usize_dec_lt(v_i_323_, v_sz_322_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v_b_324_);
return v___x_333_;
}
else
{
lean_object* v_snd_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_368_; 
v_snd_334_ = lean_ctor_get(v_b_324_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_b_324_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; 
v_unused_369_ = lean_ctor_get(v_b_324_, 0);
lean_dec(v_unused_369_);
v___x_336_ = v_b_324_;
v_isShared_337_ = v_isSharedCheck_368_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snd_334_);
lean_dec(v_b_324_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_368_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_a_338_; lean_object* v___x_339_; 
v_a_338_ = lean_array_uget_borrowed(v_as_321_, v_i_323_);
lean_inc(v_snd_334_);
lean_inc(v_a_338_);
v___x_339_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_320_, v_a_338_, v_snd_334_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_359_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_359_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_359_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_359_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
if (lean_obj_tag(v_a_340_) == 0)
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v_a_340_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_344_);
v___x_346_ = v___x_336_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_snd_334_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_346_);
v___x_348_ = v___x_342_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
lean_del_object(v___x_342_);
lean_dec(v_snd_334_);
v_a_351_ = lean_ctor_get(v_a_340_, 0);
lean_inc(v_a_351_);
lean_dec_ref(v_a_340_);
v___x_352_ = lean_box(0);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_a_351_);
lean_ctor_set(v___x_336_, 0, v___x_352_);
v___x_354_ = v___x_336_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_a_351_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
size_t v___x_355_; size_t v___x_356_; 
v___x_355_ = ((size_t)1ULL);
v___x_356_ = lean_usize_add(v_i_323_, v___x_355_);
v_i_323_ = v___x_356_;
v_b_324_ = v___x_354_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_del_object(v___x_336_);
lean_dec(v_snd_334_);
v_a_360_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_339_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_339_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2___boxed(lean_object* v_firstChoiceOnly_370_, lean_object* v_as_371_, lean_object* v_sz_372_, lean_object* v_i_373_, lean_object* v_b_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_382_; size_t v_sz_boxed_383_; size_t v_i_boxed_384_; lean_object* v_res_385_; 
v_firstChoiceOnly_boxed_382_ = lean_unbox(v_firstChoiceOnly_370_);
v_sz_boxed_383_ = lean_unbox_usize(v_sz_372_);
lean_dec(v_sz_372_);
v_i_boxed_384_ = lean_unbox_usize(v_i_373_);
lean_dec(v_i_373_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1_spec__2(v_firstChoiceOnly_boxed_382_, v_as_371_, v_sz_boxed_383_, v_i_boxed_384_, v_b_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec_ref(v_as_371_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___boxed(lean_object* v_firstChoiceOnly_386_, lean_object* v_stx_387_, lean_object* v_b_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_396_; lean_object* v_res_397_; 
v_firstChoiceOnly_boxed_396_ = lean_unbox(v_firstChoiceOnly_386_);
v_res_397_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_boxed_396_, v_stx_387_, v_b_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds(lean_object* v_stx_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
uint8_t v___x_408_; lean_object* v___x_409_; uint8_t v_firstChoiceOnly_410_; lean_object* v_stx_411_; lean_object* v_ids_412_; lean_object* v___x_413_; 
v___x_408_ = 1;
v___x_409_ = l_Lean_Syntax_topDown(v_stx_400_, v___x_408_);
v_firstChoiceOnly_410_ = lean_ctor_get_uint8(v___x_409_, sizeof(void*)*1);
v_stx_411_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_stx_411_);
lean_dec_ref(v___x_409_);
v_ids_412_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_413_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1(v_firstChoiceOnly_410_, v_stx_411_, v_ids_412_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_422_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_422_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v_a_418_; lean_object* v___x_420_; 
v_a_418_ = lean_ctor_get(v_a_414_, 0);
lean_inc(v_a_418_);
lean_dec(v_a_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_a_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_a_423_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_413_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_413_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotationIds___boxed(lean_object* v_stx_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds(v_stx_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(lean_object* v_00_u03b1_440_, lean_object* v_ref_441_, lean_object* v_msg_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_ref_441_, v_msg_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___boxed(lean_object* v_00_u03b1_451_, lean_object* v_ref_452_, lean_object* v_msg_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0(v_00_u03b1_451_, v_ref_452_, v_msg_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v_ref_452_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(lean_object* v_00_u03b1_462_, lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___redArg(v_msg_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0___boxed(lean_object* v_00_u03b1_472_, lean_object* v_msg_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0(v_00_u03b1_472_, v_msg_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(lean_object* v_msgData_482_, lean_object* v_macroStack_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___redArg(v_msgData_482_, v_macroStack_483_, v___y_488_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_492_, lean_object* v_macroStack_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0_spec__0_spec__2(v_msgData_492_, v_macroStack_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
return v_res_501_;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__4));
v___x_513_ = l_Lean_stringToMessageData(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternVars(lean_object* v_stx_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
uint8_t v___x_522_; 
v___x_522_ = l_Lean_Syntax_isQuot(v_stx_514_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__1___closed__4));
lean_inc(v_stx_514_);
v___x_524_ = l_Lean_Syntax_isOfKind(v_stx_514_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__1));
lean_inc(v_stx_514_);
v___x_526_ = l_Lean_Syntax_isOfKind(v_stx_514_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getPatternVars___closed__3));
lean_inc(v_stx_514_);
v___x_528_ = l_Lean_Syntax_isOfKind(v_stx_514_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_529_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_514_);
v___x_530_ = l_Lean_MessageData_ofSyntax(v_stx_514_);
v___x_531_ = l_Lean_indentD(v___x_530_);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_529_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_514_, v___x_532_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_stx_514_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = l_Lean_Syntax_getArg(v_stx_514_, v___x_534_);
lean_inc(v___x_535_);
v___x_536_ = l_Lean_Syntax_isOfKind(v___x_535_, v___x_525_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v___x_535_);
v___x_537_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_514_);
v___x_538_ = l_Lean_MessageData_ofSyntax(v_stx_514_);
v___x_539_ = l_Lean_indentD(v___x_538_);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_537_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_514_, v___x_540_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_stx_514_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(2u);
v___x_543_ = l_Lean_Syntax_getArg(v_stx_514_, v___x_542_);
v___x_544_ = l_Lean_Syntax_matchesNull(v___x_543_, v___x_534_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v___x_535_);
v___x_545_ = lean_obj_once(&l_Lean_Elab_Term_Quotation_getPatternVars___closed__5, &l_Lean_Elab_Term_Quotation_getPatternVars___closed__5_once, _init_l_Lean_Elab_Term_Quotation_getPatternVars___closed__5);
lean_inc(v_stx_514_);
v___x_546_ = l_Lean_MessageData_ofSyntax(v_stx_514_);
v___x_547_ = l_Lean_indentD(v___x_546_);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_545_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_getAntiquotationIds_spec__0___redArg(v_stx_514_, v___x_548_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_stx_514_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_unsigned_to_nat(3u);
v___x_551_ = l_Lean_Syntax_getArg(v_stx_514_, v___x_550_);
lean_dec(v_stx_514_);
v___x_552_ = l_Lean_Elab_Term_Quotation_getPatternVars(v___x_551_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_561_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_561_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_561_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_561_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = lean_array_push(v_a_553_, v___x_535_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
lean_dec(v___x_535_);
return v___x_552_;
}
}
}
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_mk_empty_array_with_capacity(v___x_562_);
v___x_564_ = lean_array_push(v___x_563_, v_stx_514_);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec(v_stx_514_);
v___x_566_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
else
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Elab_Term_Quotation_getAntiquotationIds(v_stx_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_a_577_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_568_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_568_);
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
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternVars___boxed(lean_object* v_stx_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_Term_Quotation_getPatternVars(v_stx_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(lean_object* v_as_594_, size_t v_i_595_, size_t v_stop_596_, lean_object* v_b_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_a_606_; uint8_t v___x_610_; 
v___x_610_ = lean_usize_dec_eq(v_i_595_, v_stop_596_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_array_uget_borrowed(v_as_594_, v_i_595_);
lean_inc(v___x_611_);
v___x_612_ = l_Lean_Elab_Term_Quotation_getPatternVars(v___x_611_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref(v___x_612_);
v___x_614_ = l_Array_append___redArg(v_b_597_, v_a_613_);
lean_dec(v_a_613_);
v_a_606_ = v___x_614_;
goto v___jp_605_;
}
else
{
lean_dec_ref(v_b_597_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_615_);
lean_dec_ref(v___x_612_);
v_a_606_ = v_a_615_;
goto v___jp_605_;
}
else
{
return v___x_612_;
}
}
}
else
{
lean_object* v___x_616_; 
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v_b_597_);
return v___x_616_;
}
v___jp_605_:
{
size_t v___x_607_; size_t v___x_608_; 
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_add(v_i_595_, v___x_607_);
v_i_595_ = v___x_608_;
v_b_597_ = v_a_606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0___boxed(lean_object* v_as_617_, lean_object* v_i_618_, lean_object* v_stop_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
size_t v_i_boxed_628_; size_t v_stop_boxed_629_; lean_object* v_res_630_; 
v_i_boxed_628_ = lean_unbox_usize(v_i_618_);
lean_dec(v_i_618_);
v_stop_boxed_629_ = lean_unbox_usize(v_stop_619_);
lean_dec(v_stop_619_);
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_as_617_, v_i_boxed_628_, v_stop_boxed_629_, v_b_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v_as_617_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars(lean_object* v_pats_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = ((lean_object*)(l_Lean_Elab_Term_Quotation_getAntiquotationIds___closed__0));
v___x_641_ = lean_array_get_size(v_pats_631_);
v___x_642_ = lean_nat_dec_lt(v___x_639_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_640_);
return v___x_643_;
}
else
{
uint8_t v___x_644_; 
v___x_644_ = lean_nat_dec_le(v___x_641_, v___x_641_);
if (v___x_644_ == 0)
{
if (v___x_642_ == 0)
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_640_);
return v___x_645_;
}
else
{
size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((size_t)0ULL);
v___x_647_ = lean_usize_of_nat(v___x_641_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_pats_631_, v___x_646_, v___x_647_, v___x_640_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
return v___x_648_;
}
}
else
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
v___x_649_ = ((size_t)0ULL);
v___x_650_ = lean_usize_of_nat(v___x_641_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_getPatternsVars_spec__0(v_pats_631_, v___x_649_, v___x_650_, v___x_640_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
return v___x_651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getPatternsVars___boxed(lean_object* v_pats_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_Elab_Term_Quotation_getPatternsVars(v_pats_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec_ref(v_pats_652_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(lean_object* v_antiquot_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v_name_665_; uint8_t v___x_666_; 
v___x_662_ = lean_unsigned_to_nat(3u);
v___x_663_ = l_Lean_Syntax_getArg(v_antiquot_661_, v___x_662_);
v___x_664_ = lean_unsigned_to_nat(1u);
v_name_665_ = l_Lean_Syntax_getArg(v___x_663_, v___x_664_);
lean_dec(v___x_663_);
v___x_666_ = l_Lean_Syntax_isMissing(v_name_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v_name_665_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; 
lean_dec(v_name_665_);
v___x_668_ = lean_box(0);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f___boxed(lean_object* v_antiquot_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Elab_Term_Quotation_getAntiquotKindSpec_x3f(v_antiquot_669_);
lean_dec(v_antiquot_669_);
return v_res_670_;
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
res = l___private_Lean_Elab_Quotation_Util_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Util_137815056____hygCtx___hyg_4_();
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
