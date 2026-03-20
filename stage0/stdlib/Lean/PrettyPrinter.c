// Lean compiler output
// Module: Lean.PrettyPrinter
// Imports: public import Lean.PrettyPrinter.Delaborator.Basic import Lean.PrettyPrinter.Delaborator public import Lean.Parser.Module public import Lean.ParserCompiler public import Lean.Util.NumObjs public import Lean.Util.ShareCommon
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
lean_object* l_Lean_Meta_ppGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_PPContext_runMetaM___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
extern lean_object* l_Lean_pp_raw;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_sanitizeSyntax(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCategory(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCategory(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_PPContext_runCoreM___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_module_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_module_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Expr_numObjs(lean_object*);
lean_object* lean_sharecommon_quick(lean_object*);
lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
uint8_t l_Lean_getPPMVarsLevels(lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ppFnsRef;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCategory___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_ppTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_PrettyPrinter_ppTerm___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_ppTerm___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_ppTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_PrettyPrinter_ppTerm___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_ppTerm___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exprSizes"};
static const lean_object* l_Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(158, 227, 30, 94, 230, 5, 70, 204)}};
static const lean_object* l_Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 146, .m_capacity = 146, .m_length = 145, .m_data = "(pretty printer) prefix each embedded expression with its sizes in the format (size disregarding sharing/size with sharing/size with max sharing)"};
static const lean_object* l_Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l_Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(206, 56, 205, 124, 93, 150, 76, 120)}};
static const lean_ctor_object l_Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(101, 167, 20, 28, 221, 60, 140, 8)}};
static const lean_object* l_Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_pp_exprSizes;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "[size "};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0 = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1 = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1_value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2 = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2_value)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3 = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3_value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4 = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4_value)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5 = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_ppExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_ppExpr___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_ppExpr___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_ppExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tagAppFns"};
static const lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value_aux_0),((lean_object*)&l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 223, 163, 149, 215, 109, 16, 158)}};
static const lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2_value;
static const lean_closure_object l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delabConst___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3_value;
static const lean_closure_object l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed, .m_arity = 11, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value),((lean_object*)&l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2_value),((lean_object*)&l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3_value)} };
static const lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_PrettyPrinter_ppExprLegacy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__0_value;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__1;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__2;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__3;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__4;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__5;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__6;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__7;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__8;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__9;
static const lean_string_object l_Lean_PrettyPrinter_ppExprLegacy___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__10 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__10_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppExprLegacy___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__10_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__11 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__11_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppExprLegacy___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__12 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__12_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__13 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__14;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__15;
static const lean_string_object l_Lean_PrettyPrinter_ppExprLegacy___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__16 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__16_value;
static const lean_string_object l_Lean_PrettyPrinter_ppExprLegacy___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<PrettyPrinter>"};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__17 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__17_value;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__18;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_PrettyPrinter_ppExprLegacy___closed__19;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__20;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_ppTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_PrettyPrinter_ppTactic___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_ppTactic___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_ppTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_PrettyPrinter_ppTactic___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_ppTactic___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_ppCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_PrettyPrinter_ppCommand___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_ppCommand___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppCommand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_ppCommand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_PrettyPrinter_ppCommand___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_ppCommand___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_ppModule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Module_module_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_ppModule___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_ppModule___closed__0_value;
static const lean_closure_object l_Lean_PrettyPrinter_ppModule___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Module_module_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PrettyPrinter_ppModule___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_ppModule___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PrettyPrinter_ppSignature___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_PrettyPrinter_ppSignature___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_ppSignature___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_ppSignature___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_PrettyPrinter_ppSignature___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_ppSignature___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delab___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(212, 152, 45, 136, 43, 176, 59, 135)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(213, 19, 19, 182, 49, 68, 234, 74)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(192, 190, 227, 235, 144, 88, 78, 130)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 83, 13, 207, 210, 46, 52, 166)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 39, 49, 159, 123, 145, 147, 151)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 228, 156, 77, 208, 58, 186, 72)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(135, 58, 92, 96, 45, 63, 110, 211)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(205, 84, 7, 14, 127, 142, 94, 81)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)(((size_t)(675687902) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(242, 80, 98, 162, 118, 230, 218, 64)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 177, 19, 210, 185, 194, 23, 23)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(221, 88, 4, 103, 22, 42, 47, 115)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(176, 211, 139, 245, 118, 121, 217, 117)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_registerParserCompilers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "parenthesizer"};
static const lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_registerParserCompilers___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_registerParserCompilers___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_registerParserCompilers___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 187, 150, 116, 216, 103, 117, 60)}};
static const lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_registerParserCompilers___closed__1_value;
static lean_once_cell_t l_Lean_PrettyPrinter_registerParserCompilers___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__2;
static const lean_string_object l_Lean_PrettyPrinter_registerParserCompilers___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_registerParserCompilers___closed__3_value;
static const lean_ctor_object l_Lean_PrettyPrinter_registerParserCompilers___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_registerParserCompilers___closed__3_value),LEAN_SCALAR_PTR_LITERAL(126, 243, 114, 121, 141, 142, 42, 100)}};
static const lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__4 = (const lean_object*)&l_Lean_PrettyPrinter_registerParserCompilers___closed__4_value;
static lean_once_cell_t l_Lean_PrettyPrinter_registerParserCompilers___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers();
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers___boxed(lean_object*);
static const lean_string_object l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "[Error pretty printing: "};
static const lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0 = (const lean_object*)&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1;
static const lean_string_object l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2 = (const lean_object*)&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofFormatWithInfosM___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed(lean_object*);
static const lean_string_object l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "(invalid MessageData.lazy, missing context)"};
static const lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0 = (const lean_object*)&l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0_value)}};
static const lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1 = (const lean_object*)&l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_MessageData_ofFormatWithInfosM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_ofFormatWithInfosM___closed__0 = (const lean_object*)&l_Lean_MessageData_ofFormatWithInfosM___closed__0_value;
static const lean_closure_object l_Lean_MessageData_ofFormatWithInfosM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_ofFormatWithInfosM___closed__1 = (const lean_object*)&l_Lean_MessageData_ofFormatWithInfosM___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_ofConst_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_ofConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "[Error pretty printing: expression not a constant]"};
static const lean_object* l_Lean_MessageData_ofConst___closed__0 = (const lean_object*)&l_Lean_MessageData_ofConst___closed__0_value;
static lean_once_cell_t l_Lean_MessageData_ofConst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofConst___closed__1;
static lean_once_cell_t l_Lean_MessageData_ofConst___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofConst___closed__2;
static lean_once_cell_t l_Lean_MessageData_ofConst___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofConst___closed__3;
static const lean_string_object l_Lean_MessageData_ofConst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.PrettyPrinter"};
static const lean_object* l_Lean_MessageData_ofConst___closed__4 = (const lean_object*)&l_Lean_MessageData_ofConst___closed__4_value;
static const lean_string_object l_Lean_MessageData_ofConst___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.MessageData.ofConst"};
static const lean_object* l_Lean_MessageData_ofConst___closed__5 = (const lean_object*)&l_Lean_MessageData_ofConst___closed__5_value;
static const lean_string_object l_Lean_MessageData_ofConst___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "not a constant"};
static const lean_object* l_Lean_MessageData_ofConst___closed__6 = (const lean_object*)&l_Lean_MessageData_ofConst___closed__6_value;
static lean_once_cell_t l_Lean_MessageData_ofConst___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_ofConst___closed__7;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConst(lean_object*);
static const lean_string_object l_Lean_MessageData_signature___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "[Error pretty printing signature: "};
static const lean_object* l_Lean_MessageData_signature___lam__0___closed__0 = (const lean_object*)&l_Lean_MessageData_signature___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_MessageData_signature___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_signature___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_signature(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object* v_cat_1_, lean_object* v_stx_2_, lean_object* v_a_3_, lean_object* v_a_4_){
_start:
{
lean_object* v_options_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_fst_10_; lean_object* v___x_11_; 
v_options_6_ = lean_ctor_get(v_a_3_, 2);
v___x_7_ = lean_box(1);
lean_inc_ref(v_options_6_);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v_options_6_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
lean_ctor_set(v___x_8_, 2, v___x_7_);
v___x_9_ = l_Lean_sanitizeSyntax(v_stx_2_, v___x_8_);
v_fst_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_fst_10_);
lean_dec_ref(v___x_9_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
lean_inc(v_cat_1_);
v___x_11_ = l_Lean_PrettyPrinter_parenthesizeCategory(v_cat_1_, v_fst_10_, v_a_3_, v_a_4_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_13_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_a_12_);
lean_dec_ref(v___x_11_);
v___x_13_ = l_Lean_PrettyPrinter_formatCategory(v_cat_1_, v_a_12_, v_a_3_, v_a_4_);
return v___x_13_;
}
else
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
lean_dec(v_a_4_);
lean_dec_ref(v_a_3_);
lean_dec(v_cat_1_);
v_a_14_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_21_ == 0)
{
v___x_16_ = v___x_11_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_11_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_a_14_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCategory___boxed(lean_object* v_cat_22_, lean_object* v_stx_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_PrettyPrinter_ppCategory(v_cat_22_, v_stx_23_, v_a_24_, v_a_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object* v_stx_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = ((lean_object*)(l_Lean_PrettyPrinter_ppTerm___closed__1));
v___x_36_ = l_Lean_PrettyPrinter_ppCategory(v___x_35_, v_stx_31_, v_a_32_, v_a_33_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTerm___boxed(lean_object* v_stx_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_PrettyPrinter_ppTerm(v_stx_37_, v_a_38_, v_a_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(lean_object* v_lctx_42_, lean_object* v_x_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_keyedConfig_49_; uint8_t v_trackZetaDelta_50_; lean_object* v_zetaDeltaSet_51_; lean_object* v_localInstances_52_; lean_object* v_defEqCtx_x3f_53_; lean_object* v_synthPendingDepth_54_; lean_object* v_canUnfold_x3f_55_; uint8_t v_univApprox_56_; uint8_t v_inTypeClassResolution_57_; uint8_t v_cacheInferType_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_66_; 
v_keyedConfig_49_ = lean_ctor_get(v___y_44_, 0);
v_trackZetaDelta_50_ = lean_ctor_get_uint8(v___y_44_, sizeof(void*)*7);
v_zetaDeltaSet_51_ = lean_ctor_get(v___y_44_, 1);
v_localInstances_52_ = lean_ctor_get(v___y_44_, 3);
v_defEqCtx_x3f_53_ = lean_ctor_get(v___y_44_, 4);
v_synthPendingDepth_54_ = lean_ctor_get(v___y_44_, 5);
v_canUnfold_x3f_55_ = lean_ctor_get(v___y_44_, 6);
v_univApprox_56_ = lean_ctor_get_uint8(v___y_44_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_57_ = lean_ctor_get_uint8(v___y_44_, sizeof(void*)*7 + 2);
v_cacheInferType_58_ = lean_ctor_get_uint8(v___y_44_, sizeof(void*)*7 + 3);
v_isSharedCheck_66_ = !lean_is_exclusive(v___y_44_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; 
v_unused_67_ = lean_ctor_get(v___y_44_, 2);
lean_dec(v_unused_67_);
v___x_60_ = v___y_44_;
v_isShared_61_ = v_isSharedCheck_66_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_canUnfold_x3f_55_);
lean_inc(v_synthPendingDepth_54_);
lean_inc(v_defEqCtx_x3f_53_);
lean_inc(v_localInstances_52_);
lean_inc(v_zetaDeltaSet_51_);
lean_inc(v_keyedConfig_49_);
lean_dec(v___y_44_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_66_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 2, v_lctx_42_);
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_keyedConfig_49_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_zetaDeltaSet_51_);
lean_ctor_set(v_reuseFailAlloc_65_, 2, v_lctx_42_);
lean_ctor_set(v_reuseFailAlloc_65_, 3, v_localInstances_52_);
lean_ctor_set(v_reuseFailAlloc_65_, 4, v_defEqCtx_x3f_53_);
lean_ctor_set(v_reuseFailAlloc_65_, 5, v_synthPendingDepth_54_);
lean_ctor_set(v_reuseFailAlloc_65_, 6, v_canUnfold_x3f_55_);
lean_ctor_set_uint8(v_reuseFailAlloc_65_, sizeof(void*)*7, v_trackZetaDelta_50_);
lean_ctor_set_uint8(v_reuseFailAlloc_65_, sizeof(void*)*7 + 1, v_univApprox_56_);
lean_ctor_set_uint8(v_reuseFailAlloc_65_, sizeof(void*)*7 + 2, v_inTypeClassResolution_57_);
lean_ctor_set_uint8(v_reuseFailAlloc_65_, sizeof(void*)*7 + 3, v_cacheInferType_58_);
v___x_63_ = v_reuseFailAlloc_65_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; 
v___x_64_ = lean_apply_5(v_x_43_, v___x_63_, v___y_45_, v___y_46_, v___y_47_, lean_box(0));
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg___boxed(lean_object* v_lctx_68_, lean_object* v_x_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(v_lctx_68_, v_x_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0(lean_object* v_00_u03b1_76_, lean_object* v_lctx_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(v_lctx_77_, v_x_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___boxed(lean_object* v_00_u03b1_85_, lean_object* v_lctx_86_, lean_object* v_x_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0(v_00_u03b1_85_, v_lctx_86_, v_x_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lam__0(lean_object* v_delab_94_, lean_object* v_e_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v___x_101_; 
lean_inc(v___y_99_);
lean_inc_ref(v___y_98_);
v___x_101_ = lean_apply_6(v_delab_94_, v_e_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, lean_box(0));
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref(v___x_101_);
v___x_103_ = l_Lean_PrettyPrinter_ppTerm(v_a_102_, v___y_98_, v___y_99_);
return v___x_103_;
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
v_a_104_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_101_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_101_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lam__0___boxed(lean_object* v_delab_112_, lean_object* v_e_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_PrettyPrinter_ppUsing___lam__0(v_delab_112_, v_e_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing(lean_object* v_e_120_, lean_object* v_delab_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_lctx_127_; lean_object* v_options_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v_fst_132_; lean_object* v___f_133_; lean_object* v___x_134_; 
v_lctx_127_ = lean_ctor_get(v_a_122_, 2);
v_options_128_ = lean_ctor_get(v_a_124_, 2);
v___x_129_ = lean_box(1);
lean_inc_ref(v_options_128_);
v___x_130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_130_, 0, v_options_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
lean_ctor_set(v___x_130_, 2, v___x_129_);
lean_inc_ref(v_lctx_127_);
v___x_131_ = l_Lean_LocalContext_sanitizeNames(v_lctx_127_, v___x_130_);
v_fst_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_fst_132_);
lean_dec_ref(v___x_131_);
v___f_133_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppUsing___lam__0___boxed), 7, 2);
lean_closure_set(v___f_133_, 0, v_delab_121_);
lean_closure_set(v___f_133_, 1, v_e_120_);
v___x_134_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(v_fst_132_, v___f_133_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___boxed(lean_object* v_e_135_, lean_object* v_delab_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_PrettyPrinter_ppUsing(v_e_135_, v_delab_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(lean_object* v_name_143_, lean_object* v_decl_144_, lean_object* v_ref_145_){
_start:
{
lean_object* v_defValue_147_; lean_object* v_descr_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_175_; 
v_defValue_147_ = lean_ctor_get(v_decl_144_, 0);
v_descr_148_ = lean_ctor_get(v_decl_144_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_decl_144_);
if (v_isSharedCheck_175_ == 0)
{
v___x_150_ = v_decl_144_;
v_isShared_151_ = v_isSharedCheck_175_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_descr_148_);
lean_inc(v_defValue_147_);
lean_dec(v_decl_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_175_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = lean_alloc_ctor(1, 0, 1);
v___x_153_ = lean_unbox(v_defValue_147_);
lean_ctor_set_uint8(v___x_152_, 0, v___x_153_);
lean_inc(v_name_143_);
v___x_154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_154_, 0, v_name_143_);
lean_ctor_set(v___x_154_, 1, v_ref_145_);
lean_ctor_set(v___x_154_, 2, v___x_152_);
lean_ctor_set(v___x_154_, 3, v_descr_148_);
lean_inc(v_name_143_);
v___x_155_ = lean_register_option(v_name_143_, v___x_154_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_165_; 
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_165_ == 0)
{
lean_object* v_unused_166_; 
v_unused_166_ = lean_ctor_get(v___x_155_, 0);
lean_dec(v_unused_166_);
v___x_157_ = v___x_155_;
v_isShared_158_ = v_isSharedCheck_165_;
goto v_resetjp_156_;
}
else
{
lean_dec(v___x_155_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_165_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v_defValue_147_);
lean_ctor_set(v___x_150_, 0, v_name_143_);
v___x_160_ = v___x_150_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_name_143_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_defValue_147_);
v___x_160_ = v_reuseFailAlloc_164_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_162_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_160_);
v___x_162_ = v___x_157_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_del_object(v___x_150_);
lean_dec(v_defValue_147_);
lean_dec(v_name_143_);
v_a_167_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_155_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_155_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_176_, lean_object* v_decl_177_, lean_object* v_ref_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Option_register___at___00Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(v_name_176_, v_decl_177_, v_ref_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = ((lean_object*)(l_Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_));
v___x_200_ = ((lean_object*)(l_Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_));
v___x_201_ = ((lean_object*)(l_Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_));
v___x_202_ = l_Lean_Option_register___at___00Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(v___x_199_, v___x_200_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4____boxed(lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_();
return v_res_204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(lean_object* v_opts_205_, lean_object* v_opt_206_){
_start:
{
lean_object* v_name_207_; lean_object* v_defValue_208_; lean_object* v_map_209_; lean_object* v___x_210_; 
v_name_207_ = lean_ctor_get(v_opt_206_, 0);
v_defValue_208_ = lean_ctor_get(v_opt_206_, 1);
v_map_209_ = lean_ctor_get(v_opts_205_, 0);
v___x_210_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_209_, v_name_207_);
if (lean_obj_tag(v___x_210_) == 0)
{
uint8_t v___x_211_; 
v___x_211_ = lean_unbox(v_defValue_208_);
return v___x_211_;
}
else
{
lean_object* v_val_212_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_212_);
lean_dec_ref(v___x_210_);
if (lean_obj_tag(v_val_212_) == 1)
{
uint8_t v_v_213_; 
v_v_213_ = lean_ctor_get_uint8(v_val_212_, 0);
lean_dec_ref(v_val_212_);
return v_v_213_;
}
else
{
uint8_t v___x_214_; 
lean_dec(v_val_212_);
v___x_214_ = lean_unbox(v_defValue_208_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0___boxed(lean_object* v_opts_215_, lean_object* v_opt_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_opts_215_, v_opt_216_);
lean_dec_ref(v_opt_216_);
lean_dec_ref(v_opts_215_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(lean_object* v_e_228_, lean_object* v_f_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_options_232_; lean_object* v_ref_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_options_232_ = lean_ctor_get(v_a_230_, 2);
v_ref_233_ = lean_ctor_get(v_a_230_, 5);
v___x_234_ = l_Lean_PrettyPrinter_pp_exprSizes;
v___x_235_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_options_232_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_dec_ref(v_e_228_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v_f_229_);
return v___x_236_;
}
else
{
lean_object* v___x_237_; 
lean_inc_ref(v_e_228_);
v___x_237_ = l_Lean_Expr_numObjs(v_e_228_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref(v___x_237_);
v___x_239_ = lean_sharecommon_quick(v_e_228_);
v___x_240_ = l_Lean_Expr_numObjs(v___x_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_265_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_265_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_265_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_265_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_245_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1));
v___x_246_ = l_Lean_Expr_sizeWithoutSharing(v_e_228_);
lean_dec_ref(v_e_228_);
v___x_247_ = l_Nat_reprFast(v___x_246_);
v___x_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_245_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3));
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = l_Nat_reprFast(v_a_238_);
v___x_253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_251_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_250_);
v___x_256_ = l_Nat_reprFast(v_a_241_);
v___x_257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_255_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5));
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_f_229_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_261_);
v___x_263_ = v___x_243_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_a_238_);
lean_dec(v_f_229_);
lean_dec_ref(v_e_228_);
v_a_266_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_277_ == 0)
{
v___x_268_ = v___x_240_;
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_240_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_270_ = lean_io_error_to_string(v_a_266_);
v___x_271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___x_272_ = l_Lean_MessageData_ofFormat(v___x_271_);
lean_inc(v_ref_233_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_ref_233_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_273_);
v___x_275_ = v___x_268_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_289_; 
lean_dec(v_f_229_);
lean_dec_ref(v_e_228_);
v_a_278_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_289_ == 0)
{
v___x_280_ = v___x_237_;
v_isShared_281_ = v_isSharedCheck_289_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_237_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_289_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_282_ = lean_io_error_to_string(v_a_278_);
v___x_283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
v___x_284_ = l_Lean_MessageData_ofFormat(v___x_283_);
lean_inc(v_ref_233_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v_ref_233_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_285_);
v___x_287_ = v___x_280_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_285_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___boxed(lean_object* v_e_290_, lean_object* v_f_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(v_e_290_, v_f_291_, v_a_292_);
lean_dec_ref(v_a_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(lean_object* v_e_295_, lean_object* v_f_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(v_e_295_, v_f_296_, v_a_299_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___boxed(lean_object* v_e_303_, lean_object* v_f_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(v_e_303_, v_f_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lam__0(lean_object* v_e_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_box(1);
v___x_318_ = l_Lean_PrettyPrinter_delab(v_e_311_, v___x_317_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lam__0___boxed(lean_object* v_e_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_PrettyPrinter_ppExpr___lam__0(v_e_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object* v_e_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___f_333_; lean_object* v___x_334_; 
v___f_333_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExpr___closed__0));
lean_inc_ref(v_a_330_);
lean_inc_ref(v_e_327_);
v___x_334_ = l_Lean_PrettyPrinter_ppUsing(v_e_327_, v___f_333_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref(v___x_334_);
v___x_336_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(v_e_327_, v_a_335_, v_a_330_);
lean_dec_ref(v_a_330_);
return v___x_336_;
}
else
{
lean_dec_ref(v_a_330_);
lean_dec_ref(v_e_327_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___boxed(lean_object* v_e_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_PrettyPrinter_ppExpr(v_e_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(lean_object* v_e_344_, lean_object* v_optsPerPos_345_, lean_object* v_delab_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
lean_inc(v___y_350_);
lean_inc_ref(v___y_349_);
lean_inc_ref(v_e_344_);
v___x_352_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_344_, v_optsPerPos_345_, v_delab_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v_fst_354_; lean_object* v_snd_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_383_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref(v___x_352_);
v_fst_354_ = lean_ctor_get(v_a_353_, 0);
v_snd_355_ = lean_ctor_get(v_a_353_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_a_353_);
if (v_isSharedCheck_383_ == 0)
{
v___x_357_ = v_a_353_;
v_isShared_358_ = v_isSharedCheck_383_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_snd_355_);
lean_inc(v_fst_354_);
lean_dec(v_a_353_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_383_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___y_360_; lean_object* v___x_380_; 
lean_inc_ref(v___y_349_);
v___x_380_ = l_Lean_PrettyPrinter_ppTerm(v_fst_354_, v___y_349_, v___y_350_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref(v___x_380_);
v___x_382_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(v_e_344_, v_a_381_, v___y_349_);
lean_dec_ref(v___y_349_);
v___y_360_ = v___x_382_;
goto v___jp_359_;
}
else
{
lean_dec_ref(v___y_349_);
lean_dec_ref(v_e_344_);
v___y_360_ = v___x_380_;
goto v___jp_359_;
}
v___jp_359_:
{
if (lean_obj_tag(v___y_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_a_361_ = lean_ctor_get(v___y_360_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___y_360_);
if (v_isSharedCheck_371_ == 0)
{
v___x_363_ = v___y_360_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___y_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v_a_361_);
v___x_366_ = v___x_357_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_361_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_snd_355_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_366_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
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
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_del_object(v___x_357_);
lean_dec(v_snd_355_);
v_a_372_ = lean_ctor_get(v___y_360_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___y_360_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___y_360_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___y_360_);
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
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec_ref(v_e_344_);
v_a_384_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_352_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_352_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lam__0___boxed(lean_object* v_e_392_, lean_object* v_optsPerPos_393_, lean_object* v_delab_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(v_e_392_, v_optsPerPos_393_, v_delab_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object* v_e_401_, lean_object* v_optsPerPos_402_, lean_object* v_delab_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_lctx_409_; lean_object* v_options_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v_fst_414_; lean_object* v___f_415_; lean_object* v___x_416_; 
v_lctx_409_ = lean_ctor_get(v_a_404_, 2);
v_options_410_ = lean_ctor_get(v_a_406_, 2);
v___x_411_ = lean_box(1);
lean_inc_ref(v_options_410_);
v___x_412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_412_, 0, v_options_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
lean_ctor_set(v___x_412_, 2, v___x_411_);
lean_inc_ref(v_lctx_409_);
v___x_413_ = l_Lean_LocalContext_sanitizeNames(v_lctx_409_, v___x_412_);
v_fst_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_fst_414_);
lean_dec_ref(v___x_413_);
v___f_415_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___lam__0___boxed), 8, 3);
lean_closure_set(v___f_415_, 0, v_e_401_);
lean_closure_set(v___f_415_, 1, v_optsPerPos_402_);
lean_closure_set(v___f_415_, 2, v_delab_403_);
v___x_416_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(v_fst_414_, v___f_415_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___boxed(lean_object* v_e_417_, lean_object* v_optsPerPos_418_, lean_object* v_delab_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_PrettyPrinter_ppExprWithInfos(v_e_417_, v_optsPerPos_418_, v_delab_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
if (lean_obj_tag(v_a_426_) == 0)
{
lean_object* v___x_428_; 
v___x_428_ = l_List_reverse___redArg(v_a_427_);
return v___x_428_;
}
else
{
lean_object* v_head_429_; lean_object* v_tail_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_439_; 
v_head_429_ = lean_ctor_get(v_a_426_, 0);
v_tail_430_ = lean_ctor_get(v_a_426_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_a_426_);
if (v_isSharedCheck_439_ == 0)
{
v___x_432_ = v_a_426_;
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_tail_430_);
lean_inc(v_head_429_);
lean_dec(v_a_426_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = l_Lean_mkLevelParam(v_head_429_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v_a_427_);
lean_ctor_set(v___x_432_, 0, v___x_434_);
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_a_427_);
v___x_436_ = v_reuseFailAlloc_438_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
v_a_426_ = v_tail_430_;
v_a_427_ = v___x_436_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos(lean_object* v_constName_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_457_; lean_object* v_env_458_; uint8_t v___x_459_; lean_object* v___x_460_; 
v___x_457_ = lean_st_ref_get(v_a_455_);
v_env_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc_ref(v_env_458_);
lean_dec(v___x_457_);
v___x_459_ = 0;
lean_inc(v_constName_451_);
v___x_460_ = l_Lean_Environment_find_x3f(v_env_458_, v_constName_451_, v___x_459_);
if (lean_obj_tag(v___x_460_) == 1)
{
lean_object* v_val_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_val_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_val_461_);
lean_dec_ref(v___x_460_);
v___x_462_ = ((lean_object*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4));
v___x_463_ = l_Lean_ConstantInfo_levelParams(v_val_461_);
lean_dec(v_val_461_);
v___x_464_ = lean_box(0);
v___x_465_ = l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(v___x_463_, v___x_464_);
v___x_466_ = l_Lean_Expr_const___override(v_constName_451_, v___x_465_);
v___x_467_ = lean_box(1);
v___x_468_ = l_Lean_PrettyPrinter_ppExprWithInfos(v___x_466_, v___x_467_, v___x_462_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
return v___x_468_;
}
else
{
lean_object* v_options_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_fst_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_499_; 
lean_dec(v___x_460_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
v_options_469_ = lean_ctor_get(v_a_454_, 2);
v___x_470_ = lean_mk_syntax_ident(v_constName_451_);
v___x_471_ = lean_box(1);
lean_inc_ref(v_options_469_);
v___x_472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_472_, 0, v_options_469_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
lean_ctor_set(v___x_472_, 2, v___x_471_);
v___x_473_ = l_Lean_sanitizeSyntax(v___x_470_, v___x_472_);
v_fst_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v___x_473_, 1);
lean_dec(v_unused_500_);
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_499_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_fst_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_499_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_PrettyPrinter_ppTerm___closed__1));
v___x_479_ = l_Lean_PrettyPrinter_formatCategory(v___x_478_, v_fst_474_, v_a_454_, v_a_455_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_490_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_490_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_490_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v___x_471_);
lean_ctor_set(v___x_476_, 0, v_a_480_);
v___x_485_ = v___x_476_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_480_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_471_);
v___x_485_ = v_reuseFailAlloc_489_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_485_);
v___x_487_ = v___x_482_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_del_object(v___x_476_);
v_a_491_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_479_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_479_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___boxed(lean_object* v_constName_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_PrettyPrinter_ppConstNameWithInfos(v_constName_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(lean_object* v_opts_508_, lean_object* v_opt_509_){
_start:
{
lean_object* v_name_510_; lean_object* v_defValue_511_; lean_object* v_map_512_; lean_object* v___x_513_; 
v_name_510_ = lean_ctor_get(v_opt_509_, 0);
v_defValue_511_ = lean_ctor_get(v_opt_509_, 1);
v_map_512_ = lean_ctor_get(v_opts_508_, 0);
v___x_513_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_512_, v_name_510_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_inc(v_defValue_511_);
return v_defValue_511_;
}
else
{
lean_object* v_val_514_; 
v_val_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_val_514_);
lean_dec_ref(v___x_513_);
if (lean_obj_tag(v_val_514_) == 3)
{
lean_object* v_v_515_; 
v_v_515_ = lean_ctor_get(v_val_514_, 0);
lean_inc(v_v_515_);
lean_dec_ref(v_val_514_);
return v_v_515_;
}
else
{
lean_dec(v_val_514_);
lean_inc(v_defValue_511_);
return v_defValue_511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0___boxed(lean_object* v_opts_516_, lean_object* v_opt_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(v_opts_516_, v_opt_517_);
lean_dec_ref(v_opt_517_);
lean_dec_ref(v_opts_516_);
return v_res_518_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1(void){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_521_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__1, &l_Lean_PrettyPrinter_ppExprLegacy___closed__1_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__3(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__2, &l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2);
v___x_525_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
lean_ctor_set(v___x_525_, 3, v___x_524_);
lean_ctor_set(v___x_525_, 4, v___x_524_);
lean_ctor_set(v___x_525_, 5, v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__4(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_unsigned_to_nat(32u);
v___x_527_ = lean_mk_empty_array_with_capacity(v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5(void){
_start:
{
size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_529_ = ((size_t)5ULL);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_unsigned_to_nat(32u);
v___x_532_ = lean_mk_empty_array_with_capacity(v___x_531_);
v___x_533_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__4, &l_Lean_PrettyPrinter_ppExprLegacy___closed__4_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__4);
v___x_534_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_530_);
lean_ctor_set(v___x_534_, 3, v___x_530_);
lean_ctor_set_usize(v___x_534_, 4, v___x_529_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__2, &l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2);
v___x_536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_ctor_set(v___x_536_, 2, v___x_535_);
lean_ctor_set(v___x_536_, 3, v___x_535_);
lean_ctor_set(v___x_536_, 4, v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__7(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__2, &l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_NameSet_empty;
v___x_540_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__5, &l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5);
v___x_541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
lean_ctor_set(v___x_541_, 2, v___x_539_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = l_Lean_firstFrontendMacroScope;
v___x_544_ = lean_nat_add(v___x_543_, v___x_542_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__14(void){
_start:
{
lean_object* v___x_555_; uint64_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__5, &l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5);
v___x_556_ = 0ULL;
v___x_557_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set_uint64(v___x_557_, sizeof(void*)*1, v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__15(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
v___x_558_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__5, &l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5);
v___x_559_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__2, &l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2);
v___x_560_ = 1;
v___x_561_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_559_);
lean_ctor_set(v___x_561_, 2, v___x_558_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*3, v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__18(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = l_Lean_Options_empty;
v___x_565_ = l_Lean_Core_getMaxHeartbeats(v___x_564_);
return v___x_565_;
}
}
static uint8_t _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__19(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = l_Lean_diagnostics;
v___x_567_ = l_Lean_Options_empty;
v___x_568_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v___x_567_, v___x_566_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__20(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = l_Lean_maxRecDepth;
v___x_570_ = l_Lean_Options_empty;
v___x_571_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(v___x_570_, v___x_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy(lean_object* v_env_572_, lean_object* v_mctx_573_, lean_object* v_lctx_574_, lean_object* v_opts_575_, lean_object* v_e_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v_fileName_606_; lean_object* v_fileMap_607_; lean_object* v_currRecDepth_608_; lean_object* v_ref_609_; lean_object* v_currNamespace_610_; lean_object* v_openDecls_611_; lean_object* v_initHeartbeats_612_; lean_object* v_maxHeartbeats_613_; lean_object* v_quotContext_614_; lean_object* v_currMacroScope_615_; lean_object* v_cancelTk_x3f_616_; uint8_t v_suppressElabErrors_617_; lean_object* v_inheritedTraceOptions_618_; lean_object* v___y_619_; lean_object* v___y_653_; uint8_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; uint8_t v___y_675_; lean_object* v___y_676_; uint8_t v___y_677_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_env_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___y_712_; lean_object* v___y_713_; uint8_t v___y_744_; uint8_t v___x_764_; 
v___x_578_ = lean_box(1);
v___x_579_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_580_ = 0;
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__0));
v___x_583_ = lean_box(0);
v___x_584_ = 1;
v___x_585_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_585_, 0, v___x_579_);
lean_ctor_set(v___x_585_, 1, v___x_578_);
lean_ctor_set(v___x_585_, 2, v_lctx_574_);
lean_ctor_set(v___x_585_, 3, v___x_582_);
lean_ctor_set(v___x_585_, 4, v___x_583_);
lean_ctor_set(v___x_585_, 5, v___x_581_);
lean_ctor_set(v___x_585_, 6, v___x_583_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*7, v___x_580_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*7 + 1, v___x_580_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*7 + 2, v___x_580_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*7 + 3, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__3, &l_Lean_PrettyPrinter_ppExprLegacy___closed__3_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__3);
v___x_587_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__5, &l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5);
v___x_588_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__6, &l_Lean_PrettyPrinter_ppExprLegacy___closed__6_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6);
v___x_589_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__7, &l_Lean_PrettyPrinter_ppExprLegacy___closed__7_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__7);
v___x_590_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__8, &l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8);
v___x_591_ = lean_io_get_num_heartbeats();
v___x_592_ = l_Lean_firstFrontendMacroScope;
v___x_593_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__9, &l_Lean_PrettyPrinter_ppExprLegacy___closed__9_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9);
v___x_594_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__12));
v___x_595_ = lean_box(0);
v___x_596_ = lean_box(0);
v___x_597_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__13));
v___x_598_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__14, &l_Lean_PrettyPrinter_ppExprLegacy___closed__14_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__14);
v___x_599_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__15, &l_Lean_PrettyPrinter_ppExprLegacy___closed__15_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__15);
v___x_600_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_600_, 0, v_env_572_);
lean_ctor_set(v___x_600_, 1, v___x_593_);
lean_ctor_set(v___x_600_, 2, v___x_594_);
lean_ctor_set(v___x_600_, 3, v___x_597_);
lean_ctor_set(v___x_600_, 4, v___x_598_);
lean_ctor_set(v___x_600_, 5, v___x_589_);
lean_ctor_set(v___x_600_, 6, v___x_590_);
lean_ctor_set(v___x_600_, 7, v___x_599_);
lean_ctor_set(v___x_600_, 8, v___x_582_);
v___x_601_ = lean_st_mk_ref(v___x_600_);
v___x_697_ = l_Lean_inheritedTraceOptions;
v___x_698_ = lean_st_ref_get(v___x_697_);
v___x_699_ = lean_st_ref_get(v___x_601_);
v___x_700_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__17));
v___x_701_ = l_Lean_instInhabitedFileMap_default;
v___x_702_ = l_Lean_Options_empty;
v___x_703_ = lean_unsigned_to_nat(1000u);
v___x_704_ = lean_box(0);
v___x_705_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__18, &l_Lean_PrettyPrinter_ppExprLegacy___closed__18_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__18);
v___x_706_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_706_, 0, v___x_700_);
lean_ctor_set(v___x_706_, 1, v___x_701_);
lean_ctor_set(v___x_706_, 2, v___x_702_);
lean_ctor_set(v___x_706_, 3, v___x_581_);
lean_ctor_set(v___x_706_, 4, v___x_703_);
lean_ctor_set(v___x_706_, 5, v___x_704_);
lean_ctor_set(v___x_706_, 6, v___x_595_);
lean_ctor_set(v___x_706_, 7, v___x_596_);
lean_ctor_set(v___x_706_, 8, v___x_591_);
lean_ctor_set(v___x_706_, 9, v___x_705_);
lean_ctor_set(v___x_706_, 10, v___x_595_);
lean_ctor_set(v___x_706_, 11, v___x_592_);
lean_ctor_set(v___x_706_, 12, v___x_583_);
lean_ctor_set(v___x_706_, 13, v___x_698_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*14, v___x_580_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*14 + 1, v___x_580_);
v_env_707_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_env_707_);
lean_dec(v___x_699_);
v___x_708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_708_, 0, v_mctx_573_);
lean_ctor_set(v___x_708_, 1, v___x_586_);
lean_ctor_set(v___x_708_, 2, v___x_578_);
lean_ctor_set(v___x_708_, 3, v___x_587_);
lean_ctor_set(v___x_708_, 4, v___x_588_);
v___x_709_ = l_Lean_diagnostics;
v___x_710_ = lean_uint8_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__19, &l_Lean_PrettyPrinter_ppExprLegacy___closed__19_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__19);
v___x_764_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_707_);
lean_dec_ref(v_env_707_);
if (v___x_764_ == 0)
{
if (v___x_710_ == 0)
{
lean_inc(v___x_601_);
v___y_712_ = v___x_706_;
v___y_713_ = v___x_601_;
goto v___jp_711_;
}
else
{
v___y_744_ = v___x_764_;
goto v___jp_743_;
}
}
else
{
v___y_744_ = v___x_710_;
goto v___jp_743_;
}
v___jp_602_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(v_opts_575_, v___y_605_);
lean_dec_ref(v___y_605_);
v___x_621_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_621_, 0, v_fileName_606_);
lean_ctor_set(v___x_621_, 1, v_fileMap_607_);
lean_ctor_set(v___x_621_, 2, v_opts_575_);
lean_ctor_set(v___x_621_, 3, v_currRecDepth_608_);
lean_ctor_set(v___x_621_, 4, v___x_620_);
lean_ctor_set(v___x_621_, 5, v_ref_609_);
lean_ctor_set(v___x_621_, 6, v_currNamespace_610_);
lean_ctor_set(v___x_621_, 7, v_openDecls_611_);
lean_ctor_set(v___x_621_, 8, v_initHeartbeats_612_);
lean_ctor_set(v___x_621_, 9, v_maxHeartbeats_613_);
lean_ctor_set(v___x_621_, 10, v_quotContext_614_);
lean_ctor_set(v___x_621_, 11, v_currMacroScope_615_);
lean_ctor_set(v___x_621_, 12, v_cancelTk_x3f_616_);
lean_ctor_set(v___x_621_, 13, v_inheritedTraceOptions_618_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*14, v___y_604_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*14 + 1, v_suppressElabErrors_617_);
lean_inc(v___y_603_);
v___x_622_ = l_Lean_PrettyPrinter_ppExpr(v_e_576_, v___x_585_, v___y_603_, v___x_621_, v___y_619_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_632_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_632_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_632_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_632_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_627_ = lean_st_ref_get(v___y_603_);
lean_dec(v___y_603_);
lean_dec(v___x_627_);
v___x_628_ = lean_st_ref_get(v___x_601_);
lean_dec(v___x_601_);
lean_dec(v___x_628_);
if (v_isShared_626_ == 0)
{
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_623_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_651_; 
lean_dec(v___y_603_);
lean_dec(v___x_601_);
v_a_633_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_651_ == 0)
{
v___x_635_ = v___x_622_;
v_isShared_636_ = v_isSharedCheck_651_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_622_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_651_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
if (lean_obj_tag(v_a_633_) == 0)
{
lean_object* v_msg_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v_msg_637_ = lean_ctor_get(v_a_633_, 1);
lean_inc_ref(v_msg_637_);
lean_dec_ref(v_a_633_);
v___x_638_ = l_Lean_MessageData_toString(v_msg_637_);
v___x_639_ = lean_mk_io_user_error(v___x_638_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_639_);
v___x_641_ = v___x_635_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
else
{
lean_object* v_id_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v_id_643_ = lean_ctor_get(v_a_633_, 0);
lean_inc(v_id_643_);
lean_dec_ref(v_a_633_);
v___x_644_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__16));
v___x_645_ = l_Nat_reprFast(v_id_643_);
v___x_646_ = lean_string_append(v___x_644_, v___x_645_);
lean_dec_ref(v___x_645_);
v___x_647_ = lean_mk_io_user_error(v___x_646_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_647_);
v___x_649_ = v___x_635_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
v___jp_652_:
{
lean_object* v_fileName_658_; lean_object* v_fileMap_659_; lean_object* v_currRecDepth_660_; lean_object* v_ref_661_; lean_object* v_currNamespace_662_; lean_object* v_openDecls_663_; lean_object* v_initHeartbeats_664_; lean_object* v_maxHeartbeats_665_; lean_object* v_quotContext_666_; lean_object* v_currMacroScope_667_; lean_object* v_cancelTk_x3f_668_; uint8_t v_suppressElabErrors_669_; lean_object* v_inheritedTraceOptions_670_; 
v_fileName_658_ = lean_ctor_get(v___y_656_, 0);
lean_inc_ref(v_fileName_658_);
v_fileMap_659_ = lean_ctor_get(v___y_656_, 1);
lean_inc_ref(v_fileMap_659_);
v_currRecDepth_660_ = lean_ctor_get(v___y_656_, 3);
lean_inc(v_currRecDepth_660_);
v_ref_661_ = lean_ctor_get(v___y_656_, 5);
lean_inc(v_ref_661_);
v_currNamespace_662_ = lean_ctor_get(v___y_656_, 6);
lean_inc(v_currNamespace_662_);
v_openDecls_663_ = lean_ctor_get(v___y_656_, 7);
lean_inc(v_openDecls_663_);
v_initHeartbeats_664_ = lean_ctor_get(v___y_656_, 8);
lean_inc(v_initHeartbeats_664_);
v_maxHeartbeats_665_ = lean_ctor_get(v___y_656_, 9);
lean_inc(v_maxHeartbeats_665_);
v_quotContext_666_ = lean_ctor_get(v___y_656_, 10);
lean_inc(v_quotContext_666_);
v_currMacroScope_667_ = lean_ctor_get(v___y_656_, 11);
lean_inc(v_currMacroScope_667_);
v_cancelTk_x3f_668_ = lean_ctor_get(v___y_656_, 12);
lean_inc(v_cancelTk_x3f_668_);
v_suppressElabErrors_669_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_670_ = lean_ctor_get(v___y_656_, 13);
lean_inc_ref(v_inheritedTraceOptions_670_);
lean_dec_ref(v___y_656_);
v___y_603_ = v___y_653_;
v___y_604_ = v___y_654_;
v___y_605_ = v___y_655_;
v_fileName_606_ = v_fileName_658_;
v_fileMap_607_ = v_fileMap_659_;
v_currRecDepth_608_ = v_currRecDepth_660_;
v_ref_609_ = v_ref_661_;
v_currNamespace_610_ = v_currNamespace_662_;
v_openDecls_611_ = v_openDecls_663_;
v_initHeartbeats_612_ = v_initHeartbeats_664_;
v_maxHeartbeats_613_ = v_maxHeartbeats_665_;
v_quotContext_614_ = v_quotContext_666_;
v_currMacroScope_615_ = v_currMacroScope_667_;
v_cancelTk_x3f_616_ = v_cancelTk_x3f_668_;
v_suppressElabErrors_617_ = v_suppressElabErrors_669_;
v_inheritedTraceOptions_618_ = v_inheritedTraceOptions_670_;
v___y_619_ = v___y_657_;
goto v___jp_602_;
}
v___jp_671_:
{
if (v___y_677_ == 0)
{
lean_object* v___x_678_; lean_object* v_env_679_; lean_object* v_nextMacroScope_680_; lean_object* v_ngen_681_; lean_object* v_auxDeclNGen_682_; lean_object* v_traceState_683_; lean_object* v_messages_684_; lean_object* v_infoState_685_; lean_object* v_snapshotTasks_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v___x_678_ = lean_st_ref_take(v___y_674_);
v_env_679_ = lean_ctor_get(v___x_678_, 0);
v_nextMacroScope_680_ = lean_ctor_get(v___x_678_, 1);
v_ngen_681_ = lean_ctor_get(v___x_678_, 2);
v_auxDeclNGen_682_ = lean_ctor_get(v___x_678_, 3);
v_traceState_683_ = lean_ctor_get(v___x_678_, 4);
v_messages_684_ = lean_ctor_get(v___x_678_, 6);
v_infoState_685_ = lean_ctor_get(v___x_678_, 7);
v_snapshotTasks_686_ = lean_ctor_get(v___x_678_, 8);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v___x_678_, 5);
lean_dec(v_unused_696_);
v___x_688_ = v___x_678_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_snapshotTasks_686_);
lean_inc(v_infoState_685_);
lean_inc(v_messages_684_);
lean_inc(v_traceState_683_);
lean_inc(v_auxDeclNGen_682_);
lean_inc(v_ngen_681_);
lean_inc(v_nextMacroScope_680_);
lean_inc(v_env_679_);
lean_dec(v___x_678_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = l_Lean_Kernel_enableDiag(v_env_679_, v___y_675_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 5, v___x_589_);
lean_ctor_set(v___x_688_, 0, v___x_690_);
v___x_692_ = v___x_688_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_nextMacroScope_680_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_ngen_681_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_auxDeclNGen_682_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v_traceState_683_);
lean_ctor_set(v_reuseFailAlloc_694_, 5, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_694_, 6, v_messages_684_);
lean_ctor_set(v_reuseFailAlloc_694_, 7, v_infoState_685_);
lean_ctor_set(v_reuseFailAlloc_694_, 8, v_snapshotTasks_686_);
v___x_692_ = v_reuseFailAlloc_694_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_st_ref_set(v___y_674_, v___x_692_);
v___y_653_ = v___y_673_;
v___y_654_ = v___y_675_;
v___y_655_ = v___y_676_;
v___y_656_ = v___y_672_;
v___y_657_ = v___y_674_;
goto v___jp_652_;
}
}
}
else
{
v___y_653_ = v___y_673_;
v___y_654_ = v___y_675_;
v___y_655_ = v___y_676_;
v___y_656_ = v___y_672_;
v___y_657_ = v___y_674_;
goto v___jp_652_;
}
}
v___jp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_fileName_716_; lean_object* v_fileMap_717_; lean_object* v_currRecDepth_718_; lean_object* v_ref_719_; lean_object* v_currNamespace_720_; lean_object* v_openDecls_721_; lean_object* v_initHeartbeats_722_; lean_object* v_maxHeartbeats_723_; lean_object* v_quotContext_724_; lean_object* v_currMacroScope_725_; lean_object* v_cancelTk_x3f_726_; uint8_t v_suppressElabErrors_727_; lean_object* v_inheritedTraceOptions_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_740_; 
v___x_714_ = lean_st_mk_ref(v___x_708_);
v___x_715_ = lean_st_ref_get(v___y_713_);
v_fileName_716_ = lean_ctor_get(v___y_712_, 0);
v_fileMap_717_ = lean_ctor_get(v___y_712_, 1);
v_currRecDepth_718_ = lean_ctor_get(v___y_712_, 3);
v_ref_719_ = lean_ctor_get(v___y_712_, 5);
v_currNamespace_720_ = lean_ctor_get(v___y_712_, 6);
v_openDecls_721_ = lean_ctor_get(v___y_712_, 7);
v_initHeartbeats_722_ = lean_ctor_get(v___y_712_, 8);
v_maxHeartbeats_723_ = lean_ctor_get(v___y_712_, 9);
v_quotContext_724_ = lean_ctor_get(v___y_712_, 10);
v_currMacroScope_725_ = lean_ctor_get(v___y_712_, 11);
v_cancelTk_x3f_726_ = lean_ctor_get(v___y_712_, 12);
v_suppressElabErrors_727_ = lean_ctor_get_uint8(v___y_712_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_728_ = lean_ctor_get(v___y_712_, 13);
v_isSharedCheck_740_ = !lean_is_exclusive(v___y_712_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; lean_object* v_unused_742_; 
v_unused_741_ = lean_ctor_get(v___y_712_, 4);
lean_dec(v_unused_741_);
v_unused_742_ = lean_ctor_get(v___y_712_, 2);
lean_dec(v_unused_742_);
v___x_730_ = v___y_712_;
v_isShared_731_ = v_isSharedCheck_740_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_inheritedTraceOptions_728_);
lean_inc(v_cancelTk_x3f_726_);
lean_inc(v_currMacroScope_725_);
lean_inc(v_quotContext_724_);
lean_inc(v_maxHeartbeats_723_);
lean_inc(v_initHeartbeats_722_);
lean_inc(v_openDecls_721_);
lean_inc(v_currNamespace_720_);
lean_inc(v_ref_719_);
lean_inc(v_currRecDepth_718_);
lean_inc(v_fileMap_717_);
lean_inc(v_fileName_716_);
lean_dec(v___y_712_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_740_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_env_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v_env_732_ = lean_ctor_get(v___x_715_, 0);
lean_inc_ref(v_env_732_);
lean_dec(v___x_715_);
v___x_733_ = l_Lean_maxRecDepth;
v___x_734_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__20, &l_Lean_PrettyPrinter_ppExprLegacy___closed__20_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__20);
lean_inc_ref(v_inheritedTraceOptions_728_);
lean_inc(v_cancelTk_x3f_726_);
lean_inc(v_currMacroScope_725_);
lean_inc(v_quotContext_724_);
lean_inc(v_maxHeartbeats_723_);
lean_inc(v_initHeartbeats_722_);
lean_inc(v_openDecls_721_);
lean_inc(v_currNamespace_720_);
lean_inc(v_ref_719_);
lean_inc(v_currRecDepth_718_);
lean_inc_ref(v_fileMap_717_);
lean_inc_ref(v_fileName_716_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 4, v___x_734_);
lean_ctor_set(v___x_730_, 2, v___x_702_);
v___x_736_ = v___x_730_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_fileName_716_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_fileMap_717_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_currRecDepth_718_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_739_, 5, v_ref_719_);
lean_ctor_set(v_reuseFailAlloc_739_, 6, v_currNamespace_720_);
lean_ctor_set(v_reuseFailAlloc_739_, 7, v_openDecls_721_);
lean_ctor_set(v_reuseFailAlloc_739_, 8, v_initHeartbeats_722_);
lean_ctor_set(v_reuseFailAlloc_739_, 9, v_maxHeartbeats_723_);
lean_ctor_set(v_reuseFailAlloc_739_, 10, v_quotContext_724_);
lean_ctor_set(v_reuseFailAlloc_739_, 11, v_currMacroScope_725_);
lean_ctor_set(v_reuseFailAlloc_739_, 12, v_cancelTk_x3f_726_);
lean_ctor_set(v_reuseFailAlloc_739_, 13, v_inheritedTraceOptions_728_);
lean_ctor_set_uint8(v_reuseFailAlloc_739_, sizeof(void*)*14 + 1, v_suppressElabErrors_727_);
v___x_736_ = v_reuseFailAlloc_739_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
uint8_t v___x_737_; uint8_t v___x_738_; 
lean_ctor_set_uint8(v___x_736_, sizeof(void*)*14, v___x_710_);
v___x_737_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_opts_575_, v___x_709_);
v___x_738_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_732_);
lean_dec_ref(v_env_732_);
if (v___x_738_ == 0)
{
if (v___x_737_ == 0)
{
lean_dec_ref(v___x_736_);
v___y_603_ = v___x_714_;
v___y_604_ = v___x_737_;
v___y_605_ = v___x_733_;
v_fileName_606_ = v_fileName_716_;
v_fileMap_607_ = v_fileMap_717_;
v_currRecDepth_608_ = v_currRecDepth_718_;
v_ref_609_ = v_ref_719_;
v_currNamespace_610_ = v_currNamespace_720_;
v_openDecls_611_ = v_openDecls_721_;
v_initHeartbeats_612_ = v_initHeartbeats_722_;
v_maxHeartbeats_613_ = v_maxHeartbeats_723_;
v_quotContext_614_ = v_quotContext_724_;
v_currMacroScope_615_ = v_currMacroScope_725_;
v_cancelTk_x3f_616_ = v_cancelTk_x3f_726_;
v_suppressElabErrors_617_ = v_suppressElabErrors_727_;
v_inheritedTraceOptions_618_ = v_inheritedTraceOptions_728_;
v___y_619_ = v___y_713_;
goto v___jp_602_;
}
else
{
lean_dec_ref(v_inheritedTraceOptions_728_);
lean_dec(v_cancelTk_x3f_726_);
lean_dec(v_currMacroScope_725_);
lean_dec(v_quotContext_724_);
lean_dec(v_maxHeartbeats_723_);
lean_dec(v_initHeartbeats_722_);
lean_dec(v_openDecls_721_);
lean_dec(v_currNamespace_720_);
lean_dec(v_ref_719_);
lean_dec(v_currRecDepth_718_);
lean_dec_ref(v_fileMap_717_);
lean_dec_ref(v_fileName_716_);
v___y_672_ = v___x_736_;
v___y_673_ = v___x_714_;
v___y_674_ = v___y_713_;
v___y_675_ = v___x_737_;
v___y_676_ = v___x_733_;
v___y_677_ = v___x_738_;
goto v___jp_671_;
}
}
else
{
lean_dec_ref(v_inheritedTraceOptions_728_);
lean_dec(v_cancelTk_x3f_726_);
lean_dec(v_currMacroScope_725_);
lean_dec(v_quotContext_724_);
lean_dec(v_maxHeartbeats_723_);
lean_dec(v_initHeartbeats_722_);
lean_dec(v_openDecls_721_);
lean_dec(v_currNamespace_720_);
lean_dec(v_ref_719_);
lean_dec(v_currRecDepth_718_);
lean_dec_ref(v_fileMap_717_);
lean_dec_ref(v_fileName_716_);
v___y_672_ = v___x_736_;
v___y_673_ = v___x_714_;
v___y_674_ = v___y_713_;
v___y_675_ = v___x_737_;
v___y_676_ = v___x_733_;
v___y_677_ = v___x_737_;
goto v___jp_671_;
}
}
}
}
v___jp_743_:
{
if (v___y_744_ == 0)
{
lean_object* v___x_745_; lean_object* v_env_746_; lean_object* v_nextMacroScope_747_; lean_object* v_ngen_748_; lean_object* v_auxDeclNGen_749_; lean_object* v_traceState_750_; lean_object* v_messages_751_; lean_object* v_infoState_752_; lean_object* v_snapshotTasks_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_762_; 
v___x_745_ = lean_st_ref_take(v___x_601_);
v_env_746_ = lean_ctor_get(v___x_745_, 0);
v_nextMacroScope_747_ = lean_ctor_get(v___x_745_, 1);
v_ngen_748_ = lean_ctor_get(v___x_745_, 2);
v_auxDeclNGen_749_ = lean_ctor_get(v___x_745_, 3);
v_traceState_750_ = lean_ctor_get(v___x_745_, 4);
v_messages_751_ = lean_ctor_get(v___x_745_, 6);
v_infoState_752_ = lean_ctor_get(v___x_745_, 7);
v_snapshotTasks_753_ = lean_ctor_get(v___x_745_, 8);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_745_, 5);
lean_dec(v_unused_763_);
v___x_755_ = v___x_745_;
v_isShared_756_ = v_isSharedCheck_762_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_snapshotTasks_753_);
lean_inc(v_infoState_752_);
lean_inc(v_messages_751_);
lean_inc(v_traceState_750_);
lean_inc(v_auxDeclNGen_749_);
lean_inc(v_ngen_748_);
lean_inc(v_nextMacroScope_747_);
lean_inc(v_env_746_);
lean_dec(v___x_745_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_762_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = l_Lean_Kernel_enableDiag(v_env_746_, v___x_710_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 5, v___x_589_);
lean_ctor_set(v___x_755_, 0, v___x_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_nextMacroScope_747_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_ngen_748_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_auxDeclNGen_749_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_traceState_750_);
lean_ctor_set(v_reuseFailAlloc_761_, 5, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_761_, 6, v_messages_751_);
lean_ctor_set(v_reuseFailAlloc_761_, 7, v_infoState_752_);
lean_ctor_set(v_reuseFailAlloc_761_, 8, v_snapshotTasks_753_);
v___x_759_ = v_reuseFailAlloc_761_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; 
v___x_760_ = lean_st_ref_set(v___x_601_, v___x_759_);
lean_inc(v___x_601_);
v___y_712_ = v___x_706_;
v___y_713_ = v___x_601_;
goto v___jp_711_;
}
}
}
else
{
lean_inc(v___x_601_);
v___y_712_ = v___x_706_;
v___y_713_ = v___x_601_;
goto v___jp_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy___boxed(lean_object* v_env_765_, lean_object* v_mctx_766_, lean_object* v_lctx_767_, lean_object* v_opts_768_, lean_object* v_e_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_PrettyPrinter_ppExprLegacy(v_env_765_, v_mctx_766_, v_lctx_767_, v_opts_768_, v_e_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic(lean_object* v_stx_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = ((lean_object*)(l_Lean_PrettyPrinter_ppTactic___closed__1));
v___x_780_ = l_Lean_PrettyPrinter_ppCategory(v___x_779_, v_stx_775_, v_a_776_, v_a_777_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic___boxed(lean_object* v_stx_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_PrettyPrinter_ppTactic(v_stx_781_, v_a_782_, v_a_783_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object* v_stx_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_PrettyPrinter_ppCommand___closed__1));
v___x_794_ = l_Lean_PrettyPrinter_ppCategory(v___x_793_, v_stx_789_, v_a_790_, v_a_791_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand___boxed(lean_object* v_stx_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_PrettyPrinter_ppCommand(v_stx_795_, v_a_796_, v_a_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule(lean_object* v_stx_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l_Lean_PrettyPrinter_ppModule___closed__0));
lean_inc(v_a_804_);
lean_inc_ref(v_a_803_);
v___x_807_ = l_Lean_PrettyPrinter_parenthesize(v___x_806_, v_stx_802_, v_a_803_, v_a_804_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref(v___x_807_);
v___x_809_ = ((lean_object*)(l_Lean_PrettyPrinter_ppModule___closed__1));
v___x_810_ = l_Lean_PrettyPrinter_format(v___x_809_, v_a_808_, v_a_803_, v_a_804_);
return v___x_810_;
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
v_a_811_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_807_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_807_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule___boxed(lean_object* v_stx_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_PrettyPrinter_ppModule(v_stx_819_, v_a_820_, v_a_821_);
return v_res_823_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_824_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
lean_ctor_set(v___x_829_, 2, v___x_828_);
lean_ctor_set(v___x_829_, 3, v___x_827_);
lean_ctor_set(v___x_829_, 4, v___x_827_);
lean_ctor_set(v___x_829_, 5, v___x_827_);
lean_ctor_set(v___x_829_, 6, v___x_827_);
lean_ctor_set(v___x_829_, 7, v___x_827_);
lean_ctor_set(v___x_829_, 8, v___x_827_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = lean_unsigned_to_nat(32u);
v___x_831_ = lean_mk_empty_array_with_capacity(v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_833_ = ((size_t)5ULL);
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_unsigned_to_nat(32u);
v___x_836_ = lean_mk_empty_array_with_capacity(v___x_835_);
v___x_837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_838_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_836_);
lean_ctor_set(v___x_838_, 2, v___x_834_);
lean_ctor_set(v___x_838_, 3, v___x_834_);
lean_ctor_set_usize(v___x_838_, 4, v___x_833_);
return v___x_838_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_839_ = lean_box(1);
v___x_840_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_841_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v___x_840_);
lean_ctor_set(v___x_842_, 2, v___x_839_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_845_ = l_Lean_stringToMessageData(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_848_ = l_Lean_stringToMessageData(v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_851_ = l_Lean_stringToMessageData(v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_854_ = l_Lean_stringToMessageData(v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_857_ = l_Lean_stringToMessageData(v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_863_ = l_Lean_stringToMessageData(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_864_, lean_object* v_declHint_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; lean_object* v_env_869_; uint8_t v___x_870_; 
v___x_868_ = lean_st_ref_get(v___y_866_);
v_env_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc_ref(v_env_869_);
lean_dec(v___x_868_);
v___x_870_ = l_Lean_Name_isAnonymous(v_declHint_865_);
if (v___x_870_ == 0)
{
uint8_t v_isExporting_871_; 
v_isExporting_871_ = lean_ctor_get_uint8(v_env_869_, sizeof(void*)*8);
if (v_isExporting_871_ == 0)
{
lean_object* v___x_872_; 
lean_dec_ref(v_env_869_);
lean_dec(v_declHint_865_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v_msg_864_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; uint8_t v___x_874_; 
lean_inc_ref(v_env_869_);
v___x_873_ = l_Lean_Environment_setExporting(v_env_869_, v___x_870_);
lean_inc(v_declHint_865_);
lean_inc_ref(v___x_873_);
v___x_874_ = l_Lean_Environment_contains(v___x_873_, v_declHint_865_, v_isExporting_871_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; 
lean_dec_ref(v___x_873_);
lean_dec_ref(v_env_869_);
lean_dec(v_declHint_865_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v_msg_864_);
return v___x_875_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_c_881_; lean_object* v___x_882_; 
v___x_876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_877_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_878_ = l_Lean_Options_empty;
v___x_879_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_879_, 0, v___x_873_);
lean_ctor_set(v___x_879_, 1, v___x_876_);
lean_ctor_set(v___x_879_, 2, v___x_877_);
lean_ctor_set(v___x_879_, 3, v___x_878_);
lean_inc(v_declHint_865_);
v___x_880_ = l_Lean_MessageData_ofConstName(v_declHint_865_, v___x_870_);
v_c_881_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_881_, 0, v___x_879_);
lean_ctor_set(v_c_881_, 1, v___x_880_);
v___x_882_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_869_, v_declHint_865_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec_ref(v_env_869_);
lean_dec(v_declHint_865_);
v___x_883_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_c_881_);
v___x_885_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = l_Lean_MessageData_note(v___x_886_);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v_msg_864_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
else
{
lean_object* v_val_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_925_; 
v_val_890_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_925_ == 0)
{
v___x_892_ = v___x_882_;
v_isShared_893_ = v_isSharedCheck_925_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_val_890_);
lean_dec(v___x_882_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_925_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_mod_897_; uint8_t v___x_898_; 
v___x_894_ = lean_box(0);
v___x_895_ = l_Lean_Environment_header(v_env_869_);
lean_dec_ref(v_env_869_);
v___x_896_ = l_Lean_EnvironmentHeader_moduleNames(v___x_895_);
v_mod_897_ = lean_array_get(v___x_894_, v___x_896_, v_val_890_);
lean_dec(v_val_890_);
lean_dec_ref(v___x_896_);
v___x_898_ = l_Lean_isPrivateName(v_declHint_865_);
lean_dec(v_declHint_865_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_899_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v_c_881_);
v___x_901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = l_Lean_MessageData_ofName(v_mod_897_);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = l_Lean_MessageData_note(v___x_906_);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v_msg_864_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 0);
lean_ctor_set(v___x_892_, 0, v___x_908_);
v___x_910_ = v___x_892_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_912_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v_c_881_);
v___x_914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_MessageData_ofName(v_mod_897_);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Lean_MessageData_note(v___x_919_);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v_msg_864_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 0);
lean_ctor_set(v___x_892_, 0, v___x_921_);
v___x_923_ = v___x_892_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_926_; 
lean_dec_ref(v_env_869_);
lean_dec(v_declHint_865_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v_msg_864_);
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_927_, lean_object* v_declHint_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_927_, v_declHint_928_, v___y_929_);
lean_dec(v___y_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_932_, lean_object* v_declHint_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_949_; 
v___x_939_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_932_, v_declHint_933_, v___y_937_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_949_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_949_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_949_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_944_ = l_Lean_unknownIdentifierMessageTag;
v___x_945_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v_a_940_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_945_);
v___x_947_ = v___x_942_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_950_, lean_object* v_declHint_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_950_, v_declHint_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; lean_object* v_env_965_; lean_object* v___x_966_; lean_object* v_mctx_967_; lean_object* v_lctx_968_; lean_object* v_options_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_964_ = lean_st_ref_get(v___y_962_);
v_env_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc_ref(v_env_965_);
lean_dec(v___x_964_);
v___x_966_ = lean_st_ref_get(v___y_960_);
v_mctx_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc_ref(v_mctx_967_);
lean_dec(v___x_966_);
v_lctx_968_ = lean_ctor_get(v___y_959_, 2);
v_options_969_ = lean_ctor_get(v___y_961_, 2);
lean_inc_ref(v_options_969_);
lean_inc_ref(v_lctx_968_);
v___x_970_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_970_, 0, v_env_965_);
lean_ctor_set(v___x_970_, 1, v_mctx_967_);
lean_ctor_set(v___x_970_, 2, v_lctx_968_);
lean_ctor_set(v___x_970_, 3, v_options_969_);
v___x_971_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v_msgData_958_);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_ref_986_; lean_object* v___x_987_; lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_996_; 
v_ref_986_ = lean_ctor_get(v___y_983_, 5);
v___x_987_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_996_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
lean_inc(v_ref_986_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_ref_986_);
lean_ctor_set(v___x_992_, 1, v_a_988_);
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 1);
lean_ctor_set(v___x_990_, 0, v___x_992_);
v___x_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1004_, lean_object* v_msg_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_fileName_1011_; lean_object* v_fileMap_1012_; lean_object* v_options_1013_; lean_object* v_currRecDepth_1014_; lean_object* v_maxRecDepth_1015_; lean_object* v_ref_1016_; lean_object* v_currNamespace_1017_; lean_object* v_openDecls_1018_; lean_object* v_initHeartbeats_1019_; lean_object* v_maxHeartbeats_1020_; lean_object* v_quotContext_1021_; lean_object* v_currMacroScope_1022_; uint8_t v_diag_1023_; lean_object* v_cancelTk_x3f_1024_; uint8_t v_suppressElabErrors_1025_; lean_object* v_inheritedTraceOptions_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1035_; 
v_fileName_1011_ = lean_ctor_get(v___y_1008_, 0);
v_fileMap_1012_ = lean_ctor_get(v___y_1008_, 1);
v_options_1013_ = lean_ctor_get(v___y_1008_, 2);
v_currRecDepth_1014_ = lean_ctor_get(v___y_1008_, 3);
v_maxRecDepth_1015_ = lean_ctor_get(v___y_1008_, 4);
v_ref_1016_ = lean_ctor_get(v___y_1008_, 5);
v_currNamespace_1017_ = lean_ctor_get(v___y_1008_, 6);
v_openDecls_1018_ = lean_ctor_get(v___y_1008_, 7);
v_initHeartbeats_1019_ = lean_ctor_get(v___y_1008_, 8);
v_maxHeartbeats_1020_ = lean_ctor_get(v___y_1008_, 9);
v_quotContext_1021_ = lean_ctor_get(v___y_1008_, 10);
v_currMacroScope_1022_ = lean_ctor_get(v___y_1008_, 11);
v_diag_1023_ = lean_ctor_get_uint8(v___y_1008_, sizeof(void*)*14);
v_cancelTk_x3f_1024_ = lean_ctor_get(v___y_1008_, 12);
v_suppressElabErrors_1025_ = lean_ctor_get_uint8(v___y_1008_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1026_ = lean_ctor_get(v___y_1008_, 13);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___y_1008_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1028_ = v___y_1008_;
v_isShared_1029_ = v_isSharedCheck_1035_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_inheritedTraceOptions_1026_);
lean_inc(v_cancelTk_x3f_1024_);
lean_inc(v_currMacroScope_1022_);
lean_inc(v_quotContext_1021_);
lean_inc(v_maxHeartbeats_1020_);
lean_inc(v_initHeartbeats_1019_);
lean_inc(v_openDecls_1018_);
lean_inc(v_currNamespace_1017_);
lean_inc(v_ref_1016_);
lean_inc(v_maxRecDepth_1015_);
lean_inc(v_currRecDepth_1014_);
lean_inc(v_options_1013_);
lean_inc(v_fileMap_1012_);
lean_inc(v_fileName_1011_);
lean_dec(v___y_1008_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1035_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_ref_1030_; lean_object* v___x_1032_; 
v_ref_1030_ = l_Lean_replaceRef(v_ref_1004_, v_ref_1016_);
lean_dec(v_ref_1016_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 5, v_ref_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_fileName_1011_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_fileMap_1012_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_options_1013_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_currRecDepth_1014_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_maxRecDepth_1015_);
lean_ctor_set(v_reuseFailAlloc_1034_, 5, v_ref_1030_);
lean_ctor_set(v_reuseFailAlloc_1034_, 6, v_currNamespace_1017_);
lean_ctor_set(v_reuseFailAlloc_1034_, 7, v_openDecls_1018_);
lean_ctor_set(v_reuseFailAlloc_1034_, 8, v_initHeartbeats_1019_);
lean_ctor_set(v_reuseFailAlloc_1034_, 9, v_maxHeartbeats_1020_);
lean_ctor_set(v_reuseFailAlloc_1034_, 10, v_quotContext_1021_);
lean_ctor_set(v_reuseFailAlloc_1034_, 11, v_currMacroScope_1022_);
lean_ctor_set(v_reuseFailAlloc_1034_, 12, v_cancelTk_x3f_1024_);
lean_ctor_set(v_reuseFailAlloc_1034_, 13, v_inheritedTraceOptions_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1034_, sizeof(void*)*14, v_diag_1023_);
lean_ctor_set_uint8(v_reuseFailAlloc_1034_, sizeof(void*)*14 + 1, v_suppressElabErrors_1025_);
v___x_1032_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1005_, v___y_1006_, v___y_1007_, v___x_1032_, v___y_1009_);
lean_dec_ref(v___x_1032_);
return v___x_1033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1036_, lean_object* v_msg_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1036_, v_msg_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v_ref_1036_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1044_, lean_object* v_msg_1045_, lean_object* v_declHint_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; lean_object* v_a_1053_; lean_object* v___x_1054_; 
v___x_1052_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1045_, v_declHint_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1044_, v_a_1053_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1055_, lean_object* v_msg_1056_, lean_object* v_declHint_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1055_, v_msg_1056_, v_declHint_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v_ref_1055_);
return v_res_1063_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1070_, lean_object* v_constName_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___x_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1077_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1078_ = 0;
lean_inc(v_constName_1071_);
v___x_1079_ = l_Lean_MessageData_ofConstName(v_constName_1071_, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1077_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1070_, v___x_1082_, v_constName_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1084_, lean_object* v_constName_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_1084_, v_constName_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v_ref_1084_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(lean_object* v_constName_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_ref_1098_; lean_object* v___x_1099_; 
v_ref_1098_ = lean_ctor_get(v___y_1095_, 5);
lean_inc(v_ref_1098_);
v___x_1099_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_1098_, v_constName_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v_ref_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(lean_object* v_constName_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; lean_object* v_env_1114_; uint8_t v___x_1115_; lean_object* v___x_1116_; 
v___x_1113_ = lean_st_ref_get(v___y_1111_);
v_env_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc_ref(v_env_1114_);
lean_dec(v___x_1113_);
v___x_1115_ = 0;
lean_inc(v_constName_1107_);
v___x_1116_ = l_Lean_Environment_find_x3f(v_env_1114_, v_constName_1107_, v___x_1115_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
return v___x_1117_;
}
else
{
lean_object* v_val_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v___y_1110_);
lean_dec(v_constName_1107_);
v_val_1118_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1116_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_val_1118_);
lean_dec(v___x_1116_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set_tag(v___x_1120_, 0);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_val_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0___boxed(lean_object* v_constName_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(v_constName_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object* v_c_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___x_1143_; 
lean_inc_ref(v_a_1140_);
lean_inc(v_c_1137_);
v___x_1143_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(v_c_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1205_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1205_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1205_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_options_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_options_1148_ = lean_ctor_get(v_a_1140_, 2);
v___x_1149_ = l_Lean_ConstantInfo_levelParams(v_a_1144_);
v___x_1150_ = lean_box(0);
v___x_1151_ = l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(v___x_1149_, v___x_1150_);
v___x_1152_ = l_Lean_Expr_const___override(v_c_1137_, v___x_1151_);
v___x_1153_ = l_Lean_pp_raw;
v___x_1154_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_options_1148_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_del_object(v___x_1146_);
lean_dec(v_a_1144_);
v___x_1155_ = lean_box(1);
v___x_1156_ = ((lean_object*)(l_Lean_PrettyPrinter_ppSignature___closed__0));
lean_inc(v_a_1141_);
lean_inc_ref(v_a_1140_);
v___x_1157_ = l_Lean_PrettyPrinter_delabCore___redArg(v___x_1152_, v___x_1155_, v___x_1156_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v_fst_1159_; lean_object* v_snd_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1184_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref(v___x_1157_);
v_fst_1159_ = lean_ctor_get(v_a_1158_, 0);
v_snd_1160_ = lean_ctor_get(v_a_1158_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_a_1158_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1162_ = v_a_1158_;
v_isShared_1163_ = v_isSharedCheck_1184_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_snd_1160_);
lean_inc(v_fst_1159_);
lean_dec(v_a_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1184_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_PrettyPrinter_ppTerm(v_fst_1159_, v_a_1140_, v_a_1141_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1175_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v_a_1165_);
v___x_1170_ = v___x_1162_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1165_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_snd_1160_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_del_object(v___x_1162_);
lean_dec(v_snd_1160_);
v_a_1176_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1164_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1164_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
v_a_1185_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1157_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1157_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
v___x_1193_ = lean_expr_dbg_to_string(v___x_1152_);
lean_dec_ref(v___x_1152_);
v___x_1194_ = ((lean_object*)(l_Lean_PrettyPrinter_ppSignature___closed__1));
v___x_1195_ = lean_string_append(v___x_1193_, v___x_1194_);
v___x_1196_ = l_Lean_ConstantInfo_type(v_a_1144_);
lean_dec(v_a_1144_);
v___x_1197_ = lean_expr_dbg_to_string(v___x_1196_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = lean_string_append(v___x_1195_, v___x_1197_);
lean_dec_ref(v___x_1197_);
v___x_1199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
v___x_1200_ = lean_box(1);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1201_);
v___x_1203_ = v___x_1146_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_c_1137_);
v_a_1206_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1143_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1143_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature___boxed(lean_object* v_c_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_PrettyPrinter_ppSignature(v_c_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(lean_object* v_00_u03b1_1221_, lean_object* v_constName_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1229_, lean_object* v_constName_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(v_00_u03b1_1229_, v_constName_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1237_, lean_object* v_ref_1238_, lean_object* v_constName_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_1238_, v_constName_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_ref_1247_, lean_object* v_constName_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(v_00_u03b1_1246_, v_ref_1247_, v_constName_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v_ref_1247_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1255_, lean_object* v_ref_1256_, lean_object* v_msg_1257_, lean_object* v_declHint_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1256_, v_msg_1257_, v_declHint_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1265_, lean_object* v_ref_1266_, lean_object* v_msg_1267_, lean_object* v_declHint_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1265_, v_ref_1266_, v_msg_1267_, v_declHint_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v_ref_1266_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1275_, lean_object* v_declHint_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1275_, v_declHint_1276_, v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1283_, lean_object* v_declHint_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1283_, v_declHint_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1291_, lean_object* v_ref_1292_, lean_object* v_msg_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1292_, v_msg_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1300_, lean_object* v_ref_1301_, lean_object* v_msg_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1300_, v_ref_1301_, v_msg_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
lean_dec(v___y_1306_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v_ref_1301_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1309_, lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1317_, v_msg_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(lean_object* v_x_1325_){
_start:
{
switch(lean_obj_tag(v_x_1325_))
{
case 3:
{
lean_object* v_a_1326_; 
v_a_1326_ = lean_ctor_get(v_x_1325_, 1);
lean_inc_ref(v_a_1326_);
lean_dec_ref(v_x_1325_);
v_x_1325_ = v_a_1326_;
goto _start;
}
case 4:
{
lean_object* v_a_1328_; lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1337_; 
v_a_1328_ = lean_ctor_get(v_x_1325_, 0);
v_a_1329_ = lean_ctor_get(v_x_1325_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_x_1325_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1331_ = v_x_1325_;
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_inc(v_a_1328_);
lean_dec(v_x_1325_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1333_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1329_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 1, v___x_1333_);
v___x_1335_ = v___x_1331_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1328_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
case 5:
{
lean_object* v_a_1338_; lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1347_; 
v_a_1338_ = lean_ctor_get(v_x_1325_, 0);
v_a_1339_ = lean_ctor_get(v_x_1325_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_x_1325_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1341_ = v_x_1325_;
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_inc(v_a_1338_);
lean_dec(v_x_1325_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1347_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1339_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v___x_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1338_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
case 6:
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1356_; 
v_a_1348_ = lean_ctor_get(v_x_1325_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_x_1325_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1350_ = v_x_1325_;
v_isShared_1351_ = v_isSharedCheck_1356_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v_x_1325_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1356_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1352_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
case 7:
{
lean_object* v_a_1357_; lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1367_; 
v_a_1357_ = lean_ctor_get(v_x_1325_, 0);
v_a_1358_ = lean_ctor_get(v_x_1325_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_x_1325_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1360_ = v_x_1325_;
v_isShared_1361_ = v_isSharedCheck_1367_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_inc(v_a_1357_);
lean_dec(v_x_1325_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1367_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1362_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1357_);
v___x_1363_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1358_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 1, v___x_1363_);
lean_ctor_set(v___x_1360_, 0, v___x_1362_);
v___x_1365_ = v___x_1360_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
case 8:
{
lean_object* v_a_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1377_; 
v_a_1368_ = lean_ctor_get(v_x_1325_, 0);
v_a_1369_ = lean_ctor_get(v_x_1325_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_x_1325_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1371_ = v_x_1325_;
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_inc(v_a_1368_);
lean_dec(v_x_1325_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1369_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v___x_1373_);
v___x_1375_ = v___x_1371_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1368_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
case 9:
{
lean_object* v_data_1378_; lean_object* v_msg_1379_; lean_object* v_children_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1391_; 
v_data_1378_ = lean_ctor_get(v_x_1325_, 0);
v_msg_1379_ = lean_ctor_get(v_x_1325_, 1);
v_children_1380_ = lean_ctor_get(v_x_1325_, 2);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_x_1325_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1382_ = v_x_1325_;
v_isShared_1383_ = v_isSharedCheck_1391_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_children_1380_);
lean_inc(v_msg_1379_);
lean_inc(v_data_1378_);
lean_dec(v_x_1325_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1391_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; size_t v_sz_1385_; size_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1384_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1379_);
v_sz_1385_ = lean_array_size(v_children_1380_);
v___x_1386_ = ((size_t)0ULL);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(v_sz_1385_, v___x_1386_, v_children_1380_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 2, v___x_1387_);
lean_ctor_set(v___x_1382_, 1, v___x_1384_);
v___x_1389_ = v___x_1382_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_data_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
default: 
{
return v_x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(size_t v_sz_1392_, size_t v_i_1393_, lean_object* v_bs_1394_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_usize_dec_lt(v_i_1393_, v_sz_1392_);
if (v___x_1395_ == 0)
{
return v_bs_1394_;
}
else
{
lean_object* v_v_1396_; lean_object* v___x_1397_; lean_object* v_bs_x27_1398_; lean_object* v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v_v_1396_ = lean_array_uget(v_bs_1394_, v_i_1393_);
v___x_1397_ = lean_unsigned_to_nat(0u);
v_bs_x27_1398_ = lean_array_uset(v_bs_1394_, v_i_1393_, v___x_1397_);
v___x_1399_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_v_1396_);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_add(v_i_1393_, v___x_1400_);
v___x_1402_ = lean_array_uset(v_bs_x27_1398_, v_i_1393_, v___x_1399_);
v_i_1393_ = v___x_1401_;
v_bs_1394_ = v___x_1402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0___boxed(lean_object* v_sz_1404_, lean_object* v_i_1405_, lean_object* v_bs_1406_){
_start:
{
size_t v_sz_boxed_1407_; size_t v_i_boxed_1408_; lean_object* v_res_1409_; 
v_sz_boxed_1407_ = lean_unbox_usize(v_sz_1404_);
lean_dec(v_sz_1404_);
v_i_boxed_1408_ = lean_unbox_usize(v_i_1405_);
lean_dec(v_i_1405_);
v_res_1409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(v_sz_boxed_1407_, v_i_boxed_1408_, v_bs_1406_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0(lean_object* v_throw_1410_, lean_object* v_x_1411_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
lean_object* v_ref_1412_; lean_object* v_msg_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1422_; 
v_ref_1412_ = lean_ctor_get(v_x_1411_, 0);
v_msg_1413_ = lean_ctor_get(v_x_1411_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_x_1411_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1415_ = v_x_1411_;
v_isShared_1416_ = v_isSharedCheck_1422_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_msg_1413_);
lean_inc(v_ref_1412_);
lean_dec(v_x_1411_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1422_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v___x_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_ref_1412_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_apply_2(v_throw_1410_, lean_box(0), v___x_1419_);
return v___x_1420_;
}
}
}
else
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_apply_2(v_throw_1410_, lean_box(0), v_x_1411_);
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(lean_object* v_inst_1424_, lean_object* v_x_1425_){
_start:
{
lean_object* v_throw_1426_; lean_object* v_tryCatch_1427_; lean_object* v___f_1428_; lean_object* v___x_1429_; 
v_throw_1426_ = lean_ctor_get(v_inst_1424_, 0);
lean_inc(v_throw_1426_);
v_tryCatch_1427_ = lean_ctor_get(v_inst_1424_, 1);
lean_inc(v_tryCatch_1427_);
lean_dec_ref(v_inst_1424_);
v___f_1428_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1428_, 0, v_throw_1426_);
v___x_1429_ = lean_apply_3(v_tryCatch_1427_, lean_box(0), v_x_1425_, v___f_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(lean_object* v_00_u03b1_1430_, lean_object* v_m_1431_, lean_object* v_inst_1432_, lean_object* v_x_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(v_inst_1432_, v_x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_apply_5(v_x_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, lean_box(0));
if (lean_obj_tag(v___x_1441_) == 0)
{
return v___x_1441_;
}
else
{
lean_object* v_a_1442_; uint8_t v___y_1444_; uint8_t v___x_1463_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
v___x_1463_ = l_Lean_Exception_isInterrupt(v_a_1442_);
if (v___x_1463_ == 0)
{
uint8_t v___x_1464_; 
lean_inc(v_a_1442_);
v___x_1464_ = l_Lean_Exception_isRuntime(v_a_1442_);
v___y_1444_ = v___x_1464_;
goto v___jp_1443_;
}
else
{
v___y_1444_ = v___x_1463_;
goto v___jp_1443_;
}
v___jp_1443_:
{
if (v___y_1444_ == 0)
{
if (lean_obj_tag(v_a_1442_) == 0)
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1461_; 
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v___x_1441_, 0);
lean_dec(v_unused_1462_);
v___x_1446_ = v___x_1441_;
v_isShared_1447_ = v_isSharedCheck_1461_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v___x_1441_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1461_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v_ref_1448_; lean_object* v_msg_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1460_; 
v_ref_1448_ = lean_ctor_get(v_a_1442_, 0);
v_msg_1449_ = lean_ctor_get(v_a_1442_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_a_1442_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1451_ = v_a_1442_;
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_msg_1449_);
lean_inc(v_ref_1448_);
lean_dec(v_a_1442_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1453_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1449_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1453_);
v___x_1455_ = v___x_1451_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_ref_1448_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1455_);
v___x_1457_ = v___x_1446_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
else
{
lean_dec(v_a_1442_);
return v___x_1441_;
}
}
else
{
lean_dec(v_a_1442_);
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___redArg(v_x_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1472_, lean_object* v_x_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___redArg(v_x_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_x_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0(v_00_u03b1_1480_, v_x_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = lean_apply_3(v_x_1488_, v___y_1489_, v___y_1490_, lean_box(0));
if (lean_obj_tag(v___x_1492_) == 0)
{
return v___x_1492_;
}
else
{
lean_object* v_a_1493_; uint8_t v___y_1495_; uint8_t v___x_1514_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
v___x_1514_ = l_Lean_Exception_isInterrupt(v_a_1493_);
if (v___x_1514_ == 0)
{
uint8_t v___x_1515_; 
lean_inc(v_a_1493_);
v___x_1515_ = l_Lean_Exception_isRuntime(v_a_1493_);
v___y_1495_ = v___x_1515_;
goto v___jp_1494_;
}
else
{
v___y_1495_ = v___x_1514_;
goto v___jp_1494_;
}
v___jp_1494_:
{
if (v___y_1495_ == 0)
{
if (lean_obj_tag(v_a_1493_) == 0)
{
lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1512_; 
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v___x_1492_, 0);
lean_dec(v_unused_1513_);
v___x_1497_ = v___x_1492_;
v_isShared_1498_ = v_isSharedCheck_1512_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v___x_1492_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1512_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_ref_1499_; lean_object* v_msg_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1511_; 
v_ref_1499_ = lean_ctor_get(v_a_1493_, 0);
v_msg_1500_ = lean_ctor_get(v_a_1493_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_a_1493_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1502_ = v_a_1493_;
v_isShared_1503_ = v_isSharedCheck_1511_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_msg_1500_);
lean_inc(v_ref_1499_);
lean_dec(v_a_1493_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1511_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 1, v___x_1504_);
v___x_1506_ = v___x_1502_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_ref_1499_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1508_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1506_);
v___x_1508_ = v___x_1497_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
else
{
lean_dec(v_a_1493_);
return v___x_1492_;
}
}
else
{
lean_dec(v_a_1493_);
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1___redArg(v_x_1516_, v___y_1517_, v___y_1518_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1521_, lean_object* v_x_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1___redArg(v_x_1522_, v___y_1523_, v___y_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1527_, lean_object* v_x_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1(v_00_u03b1_1527_, v_x_1528_, v___y_1529_, v___y_1530_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(lean_object* v_ctx_1533_, lean_object* v_l_1534_){
_start:
{
lean_object* v_opts_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; 
v_opts_1536_ = lean_ctor_get(v_ctx_1533_, 3);
v___x_1537_ = l_Lean_getPPMVarsLevels(v_opts_1536_);
v___x_1538_ = l_Lean_Level_format(v_l_1534_, v___x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object* v_ctx_1539_, lean_object* v_l_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(v_ctx_1539_, v_l_1540_);
lean_dec_ref(v_ctx_1539_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(lean_object* v_ctx_1544_, lean_object* v_e_1545_){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1547_ = lean_box(1);
v___x_1548_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1___closed__0_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_));
v___x_1549_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___boxed), 8, 3);
lean_closure_set(v___x_1549_, 0, v_e_1545_);
lean_closure_set(v___x_1549_, 1, v___x_1547_);
lean_closure_set(v___x_1549_, 2, v___x_1548_);
v___x_1550_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1550_, 0, lean_box(0));
lean_closure_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1544_, v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object* v_ctx_1552_, lean_object* v_e_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(v_ctx_1552_, v_e_1553_);
lean_dec_ref(v_ctx_1552_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(lean_object* v_ctx_1556_, lean_object* v_n_1557_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___boxed), 6, 1);
lean_closure_set(v___x_1559_, 0, v_n_1557_);
v___x_1560_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1560_, 0, lean_box(0));
lean_closure_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1556_, v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object* v_ctx_1562_, lean_object* v_n_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(v_ctx_1562_, v_n_1563_);
lean_dec_ref(v_ctx_1562_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(lean_object* v_ctx_1566_, lean_object* v_mvarId_1567_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal___boxed), 6, 1);
lean_closure_set(v___x_1569_, 0, v_mvarId_1567_);
v___x_1570_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1570_, 0, lean_box(0));
lean_closure_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1566_, v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object* v_ctx_1572_, lean_object* v_mvarId_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(v_ctx_1572_, v_mvarId_1573_);
lean_dec_ref(v_ctx_1572_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(lean_object* v_ctx_1576_, lean_object* v_stx_1577_){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTerm___boxed), 4, 1);
lean_closure_set(v___x_1579_, 0, v_stx_1577_);
v___x_1580_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2__spec__1___boxed), 5, 2);
lean_closure_set(v___x_1580_, 0, lean_box(0));
lean_closure_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_PPContext_runCoreM___redArg(v_ctx_1576_, v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object* v_ctx_1582_, lean_object* v_stx_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(v_ctx_1582_, v_stx_1583_);
lean_dec_ref(v_ctx_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1598_ = l_Lean_ppFnsRef;
v___x_1599_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_));
v___x_1600_ = lean_st_ref_set(v___x_1598_, v___x_1599_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2____boxed(lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_();
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_));
v___x_1655_ = 0;
v___x_1656_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_));
v___x_1657_ = l_Lean_registerTraceClass(v___x_1654_, v___x_1655_, v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2____boxed(lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_();
return v_res_1659_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1663_ = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
v___x_1664_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1665_ = ((lean_object*)(l_Lean_PrettyPrinter_registerParserCompilers___closed__1));
v___x_1666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v___x_1664_);
lean_ctor_set(v___x_1666_, 2, v___x_1663_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1670_ = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
v___x_1671_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1672_ = ((lean_object*)(l_Lean_PrettyPrinter_registerParserCompilers___closed__4));
v___x_1673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v___x_1671_);
lean_ctor_set(v___x_1673_, 2, v___x_1670_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers(){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_obj_once(&l_Lean_PrettyPrinter_registerParserCompilers___closed__2, &l_Lean_PrettyPrinter_registerParserCompilers___closed__2_once, _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2);
v___x_1676_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v___x_1675_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref(v___x_1676_);
v___x_1677_ = lean_obj_once(&l_Lean_PrettyPrinter_registerParserCompilers___closed__5, &l_Lean_PrettyPrinter_registerParserCompilers___closed__5_once, _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5);
v___x_1678_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v___x_1677_);
return v___x_1678_;
}
else
{
return v___x_1676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers___boxed(lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_PrettyPrinter_registerParserCompilers();
return v_res_1680_;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0(lean_object* v_fmt_1687_, lean_object* v_ctx_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1688_, v_fmt_1687_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1712_; 
v_a_1699_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1701_ = v___x_1690_;
v_isShared_1702_ = v_isSharedCheck_1712_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1690_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1712_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1703_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1, &l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1);
v___x_1704_ = lean_io_error_to_string(v_a_1699_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 3);
lean_ctor_set(v___x_1701_, 0, v___x_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1707_ = l_Lean_MessageData_ofFormat(v___x_1706_);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1703_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3, &l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3);
v___x_1710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed(lean_object* v_fmt_1713_, lean_object* v_ctx_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_MessageData_ofFormatWithInfosM___lam__0(v_fmt_1713_, v_ctx_1714_);
lean_dec_ref(v_ctx_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofFormatWithInfosM___lam__1(lean_object* v_x_1717_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = 0;
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed(lean_object* v_x_1719_){
_start:
{
uint8_t v_res_1720_; lean_object* v_r_1721_; 
v_res_1720_ = l_Lean_MessageData_ofFormatWithInfosM___lam__1(v_x_1719_);
lean_dec_ref(v_x_1719_);
v_r_1721_ = lean_box(v_res_1720_);
return v_r_1721_;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1));
v___x_1726_ = l_Lean_MessageData_ofFormat(v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2(lean_object* v_x_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2, &l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed(lean_object* v_x_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_MessageData_ofFormatWithInfosM___lam__2(v_x_1730_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM(lean_object* v_fmt_1735_){
_start:
{
lean_object* v___f_1736_; lean_object* v___f_1737_; lean_object* v___f_1738_; lean_object* v___x_1739_; 
v___f_1736_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1736_, 0, v_fmt_1735_);
v___f_1737_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__0));
v___f_1738_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__1));
v___x_1739_ = l_Lean_MessageData_lazy(v___f_1736_, v___f_1737_, v___f_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_ofConst_spec__0(lean_object* v___x_1740_, lean_object* v_msg_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_panic_fn(v___x_1740_, v_msg_1741_);
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__1(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__0));
v___x_1745_ = l_Lean_stringToMessageData(v___x_1744_);
return v___x_1745_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__2(void){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = lean_box(1);
v___x_1747_ = l_Lean_MessageData_ofFormat(v___x_1746_);
return v___x_1747_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__3(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__2, &l_Lean_MessageData_ofConst___closed__2_once, _init_l_Lean_MessageData_ofConst___closed__2);
v___x_1749_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__1, &l_Lean_MessageData_ofConst___closed__1_once, _init_l_Lean_MessageData_ofConst___closed__1);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___x_1748_);
return v___x_1750_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__7(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1754_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__6));
v___x_1755_ = lean_unsigned_to_nat(4u);
v___x_1756_ = lean_unsigned_to_nat(153u);
v___x_1757_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__5));
v___x_1758_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__4));
v___x_1759_ = l_mkPanicMessageWithDecl(v___x_1758_, v___x_1757_, v___x_1756_, v___x_1755_, v___x_1754_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConst(lean_object* v_e_1760_){
_start:
{
uint8_t v___x_1761_; 
v___x_1761_ = l_Lean_Expr_isConst(v_e_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1762_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__3, &l_Lean_MessageData_ofConst___closed__3_once, _init_l_Lean_MessageData_ofConst___closed__3);
v___x_1763_ = l_Lean_MessageData_ofExpr(v_e_1760_);
v___x_1764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1762_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__7, &l_Lean_MessageData_ofConst___closed__7_once, _init_l_Lean_MessageData_ofConst___closed__7);
v___x_1766_ = lean_panic_fn(v___x_1764_, v___x_1765_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v_delab_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1767_ = ((lean_object*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1));
v___x_1768_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1768_, 0, v___x_1761_);
v___x_1769_ = ((lean_object*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3));
v_delab_1770_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed), 11, 4);
lean_closure_set(v_delab_1770_, 0, lean_box(0));
lean_closure_set(v_delab_1770_, 1, v___x_1767_);
lean_closure_set(v_delab_1770_, 2, v___x_1768_);
lean_closure_set(v_delab_1770_, 3, v___x_1769_);
v___x_1771_ = lean_box(1);
v___x_1772_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___boxed), 8, 3);
lean_closure_set(v___x_1772_, 0, v_e_1760_);
lean_closure_set(v___x_1772_, 1, v___x_1771_);
lean_closure_set(v___x_1772_, 2, v_delab_1770_);
v___x_1773_ = l_Lean_MessageData_ofFormatWithInfosM(v___x_1772_);
return v___x_1773_;
}
}
}
static lean_object* _init_l_Lean_MessageData_signature___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_MessageData_signature___lam__0___closed__0));
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0(lean_object* v_c_1777_, lean_object* v_ctx_1778_){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_inc(v_c_1777_);
v___x_1780_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppSignature___boxed), 6, 1);
lean_closure_set(v___x_1780_, 0, v_c_1777_);
v___x_1781_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1778_, v___x_1780_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec(v_c_1777_);
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1807_; 
v_a_1790_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1792_ = v___x_1781_;
v_isShared_1793_ = v_isSharedCheck_1807_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1781_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1807_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1794_ = lean_obj_once(&l_Lean_MessageData_signature___lam__0___closed__1, &l_Lean_MessageData_signature___lam__0___closed__1_once, _init_l_Lean_MessageData_signature___lam__0___closed__1);
v___x_1795_ = lean_io_error_to_string(v_a_1790_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set_tag(v___x_1792_, 3);
lean_ctor_set(v___x_1792_, 0, v___x_1795_);
v___x_1797_ = v___x_1792_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1798_ = l_Lean_MessageData_ofFormat(v___x_1797_);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1794_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___x_1800_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3, &l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1799_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__2, &l_Lean_MessageData_ofConst___closed__2_once, _init_l_Lean_MessageData_ofConst___closed__2);
v___x_1803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1801_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = l_Lean_MessageData_ofName(v_c_1777_);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
return v___x_1805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0___boxed(lean_object* v_c_1808_, lean_object* v_ctx_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_MessageData_signature___lam__0(v_c_1808_, v_ctx_1809_);
lean_dec_ref(v_ctx_1809_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature(lean_object* v_c_1812_){
_start:
{
lean_object* v___f_1813_; lean_object* v___f_1814_; lean_object* v___f_1815_; lean_object* v___x_1816_; 
v___f_1813_ = lean_alloc_closure((void*)(l_Lean_MessageData_signature___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1813_, 0, v_c_1812_);
v___f_1814_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__0));
v___f_1815_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__1));
v___x_1816_ = l_Lean_MessageData_lazy(v___f_1813_, v___f_1814_, v___f_1815_);
return v___x_1816_;
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Delaborator(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* runtime_initialize_Lean_ParserCompiler(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_NumObjs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ShareCommon(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PrettyPrinter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Delaborator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ParserCompiler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_NumObjs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_pp_exprSizes = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_pp_exprSizes);
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_3041333433____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_PrettyPrinter_registerParserCompilers();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PrettyPrinter(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Basic(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Delaborator(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
lean_object* initialize_Lean_ParserCompiler(uint8_t builtin);
lean_object* initialize_Lean_Util_NumObjs(uint8_t builtin);
lean_object* initialize_Lean_Util_ShareCommon(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_NumObjs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PrettyPrinter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PrettyPrinter(builtin);
}
#ifdef __cplusplus
}
#endif
