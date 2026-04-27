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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_sanitizeSyntax(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCategory(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_formatCategory(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_PPContext_runCoreM___redArg(lean_object*, lean_object*);
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
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_PrettyPrinter_delabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PPContext_runMetaM___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_module_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Module_module_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Expr_numObjs(lean_object*);
lean_object* lean_sharecommon_quick(lean_object*);
lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_ppGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_diagnostics;
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
extern lean_object* l_Lean_maxRecDepth;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_ppFnsRef;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exprSizes"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(158, 227, 30, 94, 230, 5, 70, 204)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 146, .m_capacity = 146, .m_length = 145, .m_data = "(pretty printer) prefix each embedded expression with its sizes in the format (size disregarding sharing/size with sharing/size with max sharing)"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(206, 56, 205, 124, 93, 150, 76, 120)}};
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(101, 167, 20, 28, 221, 60, 140, 8)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
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
static const lean_ctor_object l_Lean_PrettyPrinter_ppExprLegacy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__0_value;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PrettyPrinter_ppExprLegacy___closed__1;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__2;
static const lean_array_object l_Lean_PrettyPrinter_ppExprLegacy___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__3 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__3_value;
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
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__10;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__11;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__12;
static const lean_string_object l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__13 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppExprLegacy___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__14 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__14_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppExprLegacy___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__15 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__15_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppExprLegacy___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__16 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__16_value;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__17;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__18;
static const lean_string_object l_Lean_PrettyPrinter_ppExprLegacy___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__19 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__19_value;
static const lean_string_object l_Lean_PrettyPrinter_ppExprLegacy___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<PrettyPrinter>"};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__20 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__20_value;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__21;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_PrettyPrinter_ppExprLegacy___closed__22;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__23;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_ppLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "level"};
static const lean_object* l_Lean_PrettyPrinter_ppLevel___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_ppLevel___closed__0_value;
static const lean_ctor_object l_Lean_PrettyPrinter_ppLevel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PrettyPrinter_ppLevel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 87, 114, 95, 43, 103, 70, 253)}};
static const lean_object* l_Lean_PrettyPrinter_ppLevel___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_ppLevel___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delab___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(201, 243, 163, 104, 244, 197, 219, 0)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(212, 152, 45, 136, 43, 176, 59, 135)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(213, 19, 19, 182, 49, 68, 234, 74)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(192, 190, 227, 235, 144, 88, 78, 130)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(118, 83, 13, 207, 210, 46, 52, 166)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 39, 49, 159, 123, 145, 147, 151)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 228, 156, 77, 208, 58, 186, 72)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(135, 58, 92, 96, 45, 63, 110, 211)}};
static const lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(205, 84, 7, 14, 127, 142, 94, 81)}};
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_ofConst_spec__0___boxed(lean_object*, lean_object*);
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
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
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
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(lean_object* v_lctx_42_, lean_object* v_x_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_keyedConfig_49_; uint8_t v_trackZetaDelta_50_; lean_object* v_zetaDeltaSet_51_; lean_object* v_localInstances_52_; lean_object* v_defEqCtx_x3f_53_; lean_object* v_synthPendingDepth_54_; lean_object* v_canUnfold_x3f_55_; uint8_t v_univApprox_56_; uint8_t v_inTypeClassResolution_57_; uint8_t v_cacheInferType_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
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
lean_inc(v_canUnfold_x3f_55_);
lean_inc(v_synthPendingDepth_54_);
lean_inc(v_defEqCtx_x3f_53_);
lean_inc_ref(v_localInstances_52_);
lean_inc(v_zetaDeltaSet_51_);
lean_inc_ref(v_keyedConfig_49_);
v___x_59_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_59_, 0, v_keyedConfig_49_);
lean_ctor_set(v___x_59_, 1, v_zetaDeltaSet_51_);
lean_ctor_set(v___x_59_, 2, v_lctx_42_);
lean_ctor_set(v___x_59_, 3, v_localInstances_52_);
lean_ctor_set(v___x_59_, 4, v_defEqCtx_x3f_53_);
lean_ctor_set(v___x_59_, 5, v_synthPendingDepth_54_);
lean_ctor_set(v___x_59_, 6, v_canUnfold_x3f_55_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*7, v_trackZetaDelta_50_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*7 + 1, v_univApprox_56_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*7 + 2, v_inTypeClassResolution_57_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*7 + 3, v_cacheInferType_58_);
lean_inc(v___y_47_);
lean_inc_ref(v___y_46_);
lean_inc(v___y_45_);
v___x_60_ = lean_apply_5(v_x_43_, v___x_59_, v___y_45_, v___y_46_, v___y_47_, lean_box(0));
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg___boxed(lean_object* v_lctx_61_, lean_object* v_x_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(v_lctx_61_, v_x_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0(lean_object* v_00_u03b1_69_, lean_object* v_lctx_70_, lean_object* v_x_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(v_lctx_70_, v_x_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___boxed(lean_object* v_00_u03b1_78_, lean_object* v_lctx_79_, lean_object* v_x_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0(v_00_u03b1_78_, v_lctx_79_, v_x_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lam__0(lean_object* v_delab_87_, lean_object* v_e_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; 
lean_inc(v___y_92_);
lean_inc_ref(v___y_91_);
v___x_94_ = lean_apply_6(v_delab_87_, v_e_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, lean_box(0));
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_96_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_95_);
lean_dec_ref(v___x_94_);
v___x_96_ = l_Lean_PrettyPrinter_ppTerm(v_a_95_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v___x_96_;
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
v_a_97_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_94_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_94_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lam__0___boxed(lean_object* v_delab_105_, lean_object* v_e_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_PrettyPrinter_ppUsing___lam__0(v_delab_105_, v_e_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing(lean_object* v_e_113_, lean_object* v_delab_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_lctx_120_; lean_object* v_options_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_fst_125_; lean_object* v___f_126_; lean_object* v___x_127_; 
v_lctx_120_ = lean_ctor_get(v_a_115_, 2);
v_options_121_ = lean_ctor_get(v_a_117_, 2);
v___x_122_ = lean_box(1);
lean_inc_ref(v_options_121_);
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v_options_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
lean_inc_ref(v_lctx_120_);
v___x_124_ = l_Lean_LocalContext_sanitizeNames(v_lctx_120_, v___x_123_);
v_fst_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_fst_125_);
lean_dec_ref(v___x_124_);
v___f_126_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppUsing___lam__0___boxed), 7, 2);
lean_closure_set(v___f_126_, 0, v_delab_114_);
lean_closure_set(v___f_126_, 1, v_e_113_);
v___x_127_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(v_fst_125_, v___f_126_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___boxed(lean_object* v_e_128_, lean_object* v_delab_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_PrettyPrinter_ppUsing(v_e_128_, v_delab_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(lean_object* v_name_136_, lean_object* v_decl_137_, lean_object* v_ref_138_){
_start:
{
lean_object* v_defValue_140_; lean_object* v_descr_141_; lean_object* v_deprecation_x3f_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_defValue_140_ = lean_ctor_get(v_decl_137_, 0);
v_descr_141_ = lean_ctor_get(v_decl_137_, 1);
v_deprecation_x3f_142_ = lean_ctor_get(v_decl_137_, 2);
v___x_143_ = lean_alloc_ctor(1, 0, 1);
v___x_144_ = lean_unbox(v_defValue_140_);
lean_ctor_set_uint8(v___x_143_, 0, v___x_144_);
lean_inc(v_deprecation_x3f_142_);
lean_inc_ref(v_descr_141_);
lean_inc_n(v_name_136_, 2);
v___x_145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_145_, 0, v_name_136_);
lean_ctor_set(v___x_145_, 1, v_ref_138_);
lean_ctor_set(v___x_145_, 2, v___x_143_);
lean_ctor_set(v___x_145_, 3, v_descr_141_);
lean_ctor_set(v___x_145_, 4, v_deprecation_x3f_142_);
v___x_146_ = lean_register_option(v_name_136_, v___x_145_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_154_; 
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; 
v_unused_155_ = lean_ctor_get(v___x_146_, 0);
lean_dec(v_unused_155_);
v___x_148_ = v___x_146_;
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
else
{
lean_dec(v___x_146_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_152_; 
lean_inc(v_defValue_140_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v_name_136_);
lean_ctor_set(v___x_150_, 1, v_defValue_140_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_150_);
v___x_152_ = v___x_148_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_name_136_);
v_a_156_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_146_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_146_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_164_, lean_object* v_decl_165_, lean_object* v_ref_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(v_name_164_, v_decl_165_, v_ref_166_);
lean_dec_ref(v_decl_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_));
v___x_189_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_));
v___x_190_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_));
v___x_191_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(v___x_188_, v___x_189_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4____boxed(lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_();
return v_res_193_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(lean_object* v_opts_194_, lean_object* v_opt_195_){
_start:
{
lean_object* v_name_196_; lean_object* v_defValue_197_; lean_object* v_map_198_; lean_object* v___x_199_; 
v_name_196_ = lean_ctor_get(v_opt_195_, 0);
v_defValue_197_ = lean_ctor_get(v_opt_195_, 1);
v_map_198_ = lean_ctor_get(v_opts_194_, 0);
v___x_199_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_198_, v_name_196_);
if (lean_obj_tag(v___x_199_) == 0)
{
uint8_t v___x_200_; 
v___x_200_ = lean_unbox(v_defValue_197_);
return v___x_200_;
}
else
{
lean_object* v_val_201_; 
v_val_201_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_201_);
lean_dec_ref(v___x_199_);
if (lean_obj_tag(v_val_201_) == 1)
{
uint8_t v_v_202_; 
v_v_202_ = lean_ctor_get_uint8(v_val_201_, 0);
lean_dec_ref(v_val_201_);
return v_v_202_;
}
else
{
uint8_t v___x_203_; 
lean_dec(v_val_201_);
v___x_203_ = lean_unbox(v_defValue_197_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0___boxed(lean_object* v_opts_204_, lean_object* v_opt_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_opts_204_, v_opt_205_);
lean_dec_ref(v_opt_205_);
lean_dec_ref(v_opts_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(lean_object* v_e_217_, lean_object* v_f_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_options_221_; lean_object* v_ref_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_options_221_ = lean_ctor_get(v_a_219_, 2);
v_ref_222_ = lean_ctor_get(v_a_219_, 5);
v___x_223_ = l_Lean_PrettyPrinter_pp_exprSizes;
v___x_224_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_options_221_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
lean_dec_ref(v_e_217_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v_f_218_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; 
lean_inc_ref(v_e_217_);
v___x_226_ = l_Lean_Expr_numObjs(v_e_217_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref(v___x_226_);
v___x_228_ = lean_sharecommon_quick(v_e_217_);
v___x_229_ = l_Lean_Expr_numObjs(v___x_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_254_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_254_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_254_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_254_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_234_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1));
v___x_235_ = l_Lean_Expr_sizeWithoutSharing(v_e_217_);
lean_dec_ref(v_e_217_);
v___x_236_ = l_Nat_reprFast(v___x_235_);
v___x_237_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_234_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3));
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = l_Nat_reprFast(v_a_227_);
v___x_242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_240_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_239_);
v___x_245_ = l_Nat_reprFast(v_a_230_);
v___x_246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
v___x_247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_244_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5));
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v_f_218_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_250_);
v___x_252_ = v___x_232_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_266_; 
lean_dec(v_a_227_);
lean_dec(v_f_218_);
lean_dec_ref(v_e_217_);
v_a_255_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_266_ == 0)
{
v___x_257_ = v___x_229_;
v_isShared_258_ = v_isSharedCheck_266_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_229_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_266_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_259_ = lean_io_error_to_string(v_a_255_);
v___x_260_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
v___x_261_ = l_Lean_MessageData_ofFormat(v___x_260_);
lean_inc(v_ref_222_);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v_ref_222_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_262_);
v___x_264_ = v___x_257_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_278_; 
lean_dec(v_f_218_);
lean_dec_ref(v_e_217_);
v_a_267_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_278_ == 0)
{
v___x_269_ = v___x_226_;
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_226_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_271_ = lean_io_error_to_string(v_a_267_);
v___x_272_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
v___x_273_ = l_Lean_MessageData_ofFormat(v___x_272_);
lean_inc(v_ref_222_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_ref_222_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_274_);
v___x_276_ = v___x_269_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___boxed(lean_object* v_e_279_, lean_object* v_f_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(v_e_279_, v_f_280_, v_a_281_);
lean_dec_ref(v_a_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(lean_object* v_e_284_, lean_object* v_f_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(v_e_284_, v_f_285_, v_a_288_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___boxed(lean_object* v_e_292_, lean_object* v_f_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(v_e_292_, v_f_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lam__0(lean_object* v_e_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_box(1);
v___x_307_ = l_Lean_PrettyPrinter_delab(v_e_300_, v___x_306_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lam__0___boxed(lean_object* v_e_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_PrettyPrinter_ppExpr___lam__0(v_e_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object* v_e_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___f_322_; lean_object* v___x_323_; 
v___f_322_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExpr___closed__0));
lean_inc_ref(v_e_316_);
v___x_323_ = l_Lean_PrettyPrinter_ppUsing(v_e_316_, v___f_322_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_325_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref(v___x_323_);
v___x_325_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(v_e_316_, v_a_324_, v_a_319_);
return v___x_325_;
}
else
{
lean_dec_ref(v_e_316_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___boxed(lean_object* v_e_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_PrettyPrinter_ppExpr(v_e_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(lean_object* v_e_333_, lean_object* v_optsPerPos_334_, lean_object* v_delab_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; 
lean_inc_ref(v_e_333_);
v___x_341_ = l_Lean_PrettyPrinter_delabCore___redArg(v_e_333_, v_optsPerPos_334_, v_delab_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v_fst_343_; lean_object* v_snd_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_372_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref(v___x_341_);
v_fst_343_ = lean_ctor_get(v_a_342_, 0);
v_snd_344_ = lean_ctor_get(v_a_342_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_a_342_);
if (v_isSharedCheck_372_ == 0)
{
v___x_346_ = v_a_342_;
v_isShared_347_ = v_isSharedCheck_372_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snd_344_);
lean_inc(v_fst_343_);
lean_dec(v_a_342_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_372_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___y_349_; lean_object* v___x_369_; 
v___x_369_ = l_Lean_PrettyPrinter_ppTerm(v_fst_343_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_371_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref(v___x_369_);
v___x_371_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(v_e_333_, v_a_370_, v___y_338_);
v___y_349_ = v___x_371_;
goto v___jp_348_;
}
else
{
lean_dec_ref(v_e_333_);
v___y_349_ = v___x_369_;
goto v___jp_348_;
}
v___jp_348_:
{
if (lean_obj_tag(v___y_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_360_; 
v_a_350_ = lean_ctor_get(v___y_349_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___y_349_);
if (v_isSharedCheck_360_ == 0)
{
v___x_352_ = v___y_349_;
v_isShared_353_ = v_isSharedCheck_360_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___y_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_360_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v_a_350_);
v___x_355_ = v___x_346_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_350_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_snd_344_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_355_);
v___x_357_ = v___x_352_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_del_object(v___x_346_);
lean_dec(v_snd_344_);
v_a_361_ = lean_ctor_get(v___y_349_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___y_349_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___y_349_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___y_349_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v_e_333_);
v_a_373_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_341_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_341_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lam__0___boxed(lean_object* v_e_381_, lean_object* v_optsPerPos_382_, lean_object* v_delab_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(v_e_381_, v_optsPerPos_382_, v_delab_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object* v_e_390_, lean_object* v_optsPerPos_391_, lean_object* v_delab_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_lctx_398_; lean_object* v_options_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_fst_403_; lean_object* v___f_404_; lean_object* v___x_405_; 
v_lctx_398_ = lean_ctor_get(v_a_393_, 2);
v_options_399_ = lean_ctor_get(v_a_395_, 2);
v___x_400_ = lean_box(1);
lean_inc_ref(v_options_399_);
v___x_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_401_, 0, v_options_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
lean_inc_ref(v_lctx_398_);
v___x_402_ = l_Lean_LocalContext_sanitizeNames(v_lctx_398_, v___x_401_);
v_fst_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_fst_403_);
lean_dec_ref(v___x_402_);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___lam__0___boxed), 8, 3);
lean_closure_set(v___f_404_, 0, v_e_390_);
lean_closure_set(v___f_404_, 1, v_optsPerPos_391_);
lean_closure_set(v___f_404_, 2, v_delab_392_);
v___x_405_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(v_fst_403_, v___f_404_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___boxed(lean_object* v_e_406_, lean_object* v_optsPerPos_407_, lean_object* v_delab_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_PrettyPrinter_ppExprWithInfos(v_e_406_, v_optsPerPos_407_, v_delab_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
if (lean_obj_tag(v_a_415_) == 0)
{
lean_object* v___x_417_; 
v___x_417_ = l_List_reverse___redArg(v_a_416_);
return v___x_417_;
}
else
{
lean_object* v_head_418_; lean_object* v_tail_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_428_; 
v_head_418_ = lean_ctor_get(v_a_415_, 0);
v_tail_419_ = lean_ctor_get(v_a_415_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_a_415_);
if (v_isSharedCheck_428_ == 0)
{
v___x_421_ = v_a_415_;
v_isShared_422_ = v_isSharedCheck_428_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_tail_419_);
lean_inc(v_head_418_);
lean_dec(v_a_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_428_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = l_Lean_mkLevelParam(v_head_418_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v_a_416_);
lean_ctor_set(v___x_421_, 0, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_a_416_);
v___x_425_ = v_reuseFailAlloc_427_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
v_a_415_ = v_tail_419_;
v_a_416_ = v___x_425_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos(lean_object* v_constName_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_446_; lean_object* v_env_447_; uint8_t v___x_448_; lean_object* v___x_449_; 
v___x_446_ = lean_st_ref_get(v_a_444_);
v_env_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc_ref(v_env_447_);
lean_dec(v___x_446_);
v___x_448_ = 0;
lean_inc(v_constName_440_);
v___x_449_ = l_Lean_Environment_find_x3f(v_env_447_, v_constName_440_, v___x_448_);
if (lean_obj_tag(v___x_449_) == 1)
{
lean_object* v_val_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_val_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_val_450_);
lean_dec_ref(v___x_449_);
v___x_451_ = ((lean_object*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4));
v___x_452_ = l_Lean_ConstantInfo_levelParams(v_val_450_);
lean_dec(v_val_450_);
v___x_453_ = lean_box(0);
v___x_454_ = l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(v___x_452_, v___x_453_);
v___x_455_ = l_Lean_Expr_const___override(v_constName_440_, v___x_454_);
v___x_456_ = lean_box(1);
v___x_457_ = l_Lean_PrettyPrinter_ppExprWithInfos(v___x_455_, v___x_456_, v___x_451_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
return v___x_457_;
}
else
{
lean_object* v_options_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_fst_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_488_; 
lean_dec(v___x_449_);
v_options_458_ = lean_ctor_get(v_a_443_, 2);
v___x_459_ = lean_mk_syntax_ident(v_constName_440_);
v___x_460_ = lean_box(1);
lean_inc_ref(v_options_458_);
v___x_461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_461_, 0, v_options_458_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
lean_ctor_set(v___x_461_, 2, v___x_460_);
v___x_462_ = l_Lean_sanitizeSyntax(v___x_459_, v___x_461_);
v_fst_463_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_488_ == 0)
{
lean_object* v_unused_489_; 
v_unused_489_ = lean_ctor_get(v___x_462_, 1);
lean_dec(v_unused_489_);
v___x_465_ = v___x_462_;
v_isShared_466_ = v_isSharedCheck_488_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_fst_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_488_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_PrettyPrinter_ppTerm___closed__1));
v___x_468_ = l_Lean_PrettyPrinter_formatCategory(v___x_467_, v_fst_463_, v_a_443_, v_a_444_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_479_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_479_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_460_);
lean_ctor_set(v___x_465_, 0, v_a_469_);
v___x_474_ = v___x_465_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_469_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_460_);
v___x_474_ = v_reuseFailAlloc_478_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_476_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_474_);
v___x_476_ = v___x_471_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
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
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_del_object(v___x_465_);
v_a_480_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_468_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_468_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___boxed(lean_object* v_constName_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_PrettyPrinter_ppConstNameWithInfos(v_constName_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(lean_object* v_opts_497_, lean_object* v_opt_498_){
_start:
{
lean_object* v_name_499_; lean_object* v_defValue_500_; lean_object* v_map_501_; lean_object* v___x_502_; 
v_name_499_ = lean_ctor_get(v_opt_498_, 0);
v_defValue_500_ = lean_ctor_get(v_opt_498_, 1);
v_map_501_ = lean_ctor_get(v_opts_497_, 0);
v___x_502_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_501_, v_name_499_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_inc(v_defValue_500_);
return v_defValue_500_;
}
else
{
lean_object* v_val_503_; 
v_val_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_val_503_);
lean_dec_ref(v___x_502_);
if (lean_obj_tag(v_val_503_) == 3)
{
lean_object* v_v_504_; 
v_v_504_ = lean_ctor_get(v_val_503_, 0);
lean_inc(v_v_504_);
lean_dec_ref(v_val_503_);
return v_v_504_;
}
else
{
lean_dec(v_val_503_);
lean_inc(v_defValue_500_);
return v_defValue_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0___boxed(lean_object* v_opts_505_, lean_object* v_opt_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(v_opts_505_, v_opt_506_);
lean_dec_ref(v_opt_506_);
lean_dec_ref(v_opts_505_);
return v_res_507_;
}
}
static uint64_t _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1(void){
_start:
{
lean_object* v___x_514_; uint64_t v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__0));
v___x_515_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2(void){
_start:
{
uint64_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = lean_uint64_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__1, &l_Lean_PrettyPrinter_ppExprLegacy___closed__1_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1);
v___x_517_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__0));
v___x_518_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set_uint64(v___x_518_, sizeof(void*)*1, v___x_516_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__4(void){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_521_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__4, &l_Lean_PrettyPrinter_ppExprLegacy___closed__4_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__4);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__5, &l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5);
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
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__7(void){
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
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8(void){
_start:
{
size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_529_ = ((size_t)5ULL);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_unsigned_to_nat(32u);
v___x_532_ = lean_mk_empty_array_with_capacity(v___x_531_);
v___x_533_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__7, &l_Lean_PrettyPrinter_ppExprLegacy___closed__7_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__7);
v___x_534_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
lean_ctor_set(v___x_534_, 2, v___x_530_);
lean_ctor_set(v___x_534_, 3, v___x_530_);
lean_ctor_set_usize(v___x_534_, 4, v___x_529_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__5, &l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5);
v___x_536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_ctor_set(v___x_536_, 2, v___x_535_);
lean_ctor_set(v___x_536_, 3, v___x_535_);
lean_ctor_set(v___x_536_, 4, v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__10(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__5, &l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__11(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_NameSet_empty;
v___x_540_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__8, &l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8);
v___x_541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
lean_ctor_set(v___x_541_, 2, v___x_539_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__12(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = l_Lean_firstFrontendMacroScope;
v___x_544_ = lean_nat_add(v___x_543_, v___x_542_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__17(void){
_start:
{
lean_object* v___x_555_; uint64_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__8, &l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8);
v___x_556_ = 0ULL;
v___x_557_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set_uint64(v___x_557_, sizeof(void*)*1, v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__18(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
v___x_558_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__8, &l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8);
v___x_559_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__5, &l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5);
v___x_560_ = 1;
v___x_561_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_559_);
lean_ctor_set(v___x_561_, 2, v___x_558_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*3, v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__21(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = l_Lean_Options_empty;
v___x_565_ = l_Lean_Core_getMaxHeartbeats(v___x_564_);
return v___x_565_;
}
}
static uint8_t _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__22(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_566_ = l_Lean_diagnostics;
v___x_567_ = l_Lean_Options_empty;
v___x_568_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v___x_567_, v___x_566_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__23(void){
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
lean_object* v___x_578_; uint8_t v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___y_603_; lean_object* v___y_604_; uint8_t v___y_605_; lean_object* v_fileName_606_; lean_object* v_fileMap_607_; lean_object* v_currRecDepth_608_; lean_object* v_ref_609_; lean_object* v_currNamespace_610_; lean_object* v_openDecls_611_; lean_object* v_initHeartbeats_612_; lean_object* v_maxHeartbeats_613_; lean_object* v_quotContext_614_; lean_object* v_currMacroScope_615_; lean_object* v_cancelTk_x3f_616_; uint8_t v_suppressElabErrors_617_; lean_object* v_inheritedTraceOptions_618_; lean_object* v___y_619_; lean_object* v___y_653_; lean_object* v___y_654_; uint8_t v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; uint8_t v___y_675_; lean_object* v___y_676_; uint8_t v___y_677_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_env_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___y_712_; lean_object* v___y_713_; uint8_t v___y_744_; uint8_t v___x_764_; 
v___x_578_ = lean_box(1);
v___x_579_ = 0;
v___x_580_ = 1;
v___x_581_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__2, &l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__3));
v___x_584_ = lean_box(0);
v___x_585_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_585_, 0, v___x_581_);
lean_ctor_set(v___x_585_, 1, v___x_578_);
lean_ctor_set(v___x_585_, 2, v_lctx_574_);
lean_ctor_set(v___x_585_, 3, v___x_583_);
lean_ctor_set(v___x_585_, 4, v___x_584_);
lean_ctor_set(v___x_585_, 5, v___x_582_);
lean_ctor_set(v___x_585_, 6, v___x_584_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*7, v___x_579_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*7 + 1, v___x_579_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*7 + 2, v___x_579_);
lean_ctor_set_uint8(v___x_585_, sizeof(void*)*7 + 3, v___x_580_);
v___x_586_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__6, &l_Lean_PrettyPrinter_ppExprLegacy___closed__6_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6);
v___x_587_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__8, &l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8);
v___x_588_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__9, &l_Lean_PrettyPrinter_ppExprLegacy___closed__9_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9);
v___x_589_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__10, &l_Lean_PrettyPrinter_ppExprLegacy___closed__10_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__10);
v___x_590_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__11, &l_Lean_PrettyPrinter_ppExprLegacy___closed__11_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__11);
v___x_591_ = lean_io_get_num_heartbeats();
v___x_592_ = l_Lean_firstFrontendMacroScope;
v___x_593_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__12, &l_Lean_PrettyPrinter_ppExprLegacy___closed__12_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__12);
v___x_594_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__15));
v___x_595_ = lean_box(0);
v___x_596_ = lean_box(0);
v___x_597_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__16));
v___x_598_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__17, &l_Lean_PrettyPrinter_ppExprLegacy___closed__17_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__17);
v___x_599_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__18, &l_Lean_PrettyPrinter_ppExprLegacy___closed__18_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__18);
v___x_600_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_600_, 0, v_env_572_);
lean_ctor_set(v___x_600_, 1, v___x_593_);
lean_ctor_set(v___x_600_, 2, v___x_594_);
lean_ctor_set(v___x_600_, 3, v___x_597_);
lean_ctor_set(v___x_600_, 4, v___x_598_);
lean_ctor_set(v___x_600_, 5, v___x_589_);
lean_ctor_set(v___x_600_, 6, v___x_590_);
lean_ctor_set(v___x_600_, 7, v___x_599_);
lean_ctor_set(v___x_600_, 8, v___x_583_);
v___x_601_ = lean_st_mk_ref(v___x_600_);
v___x_697_ = l_Lean_inheritedTraceOptions;
v___x_698_ = lean_st_ref_get(v___x_697_);
v___x_699_ = lean_st_ref_get(v___x_601_);
v___x_700_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__20));
v___x_701_ = l_Lean_instInhabitedFileMap_default;
v___x_702_ = l_Lean_Options_empty;
v___x_703_ = lean_unsigned_to_nat(1000u);
v___x_704_ = lean_box(0);
v___x_705_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__21, &l_Lean_PrettyPrinter_ppExprLegacy___closed__21_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__21);
v___x_706_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_706_, 0, v___x_700_);
lean_ctor_set(v___x_706_, 1, v___x_701_);
lean_ctor_set(v___x_706_, 2, v___x_702_);
lean_ctor_set(v___x_706_, 3, v___x_582_);
lean_ctor_set(v___x_706_, 4, v___x_703_);
lean_ctor_set(v___x_706_, 5, v___x_704_);
lean_ctor_set(v___x_706_, 6, v___x_595_);
lean_ctor_set(v___x_706_, 7, v___x_596_);
lean_ctor_set(v___x_706_, 8, v___x_591_);
lean_ctor_set(v___x_706_, 9, v___x_705_);
lean_ctor_set(v___x_706_, 10, v___x_595_);
lean_ctor_set(v___x_706_, 11, v___x_592_);
lean_ctor_set(v___x_706_, 12, v___x_584_);
lean_ctor_set(v___x_706_, 13, v___x_698_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*14, v___x_579_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*14 + 1, v___x_579_);
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
v___x_710_ = lean_uint8_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__22, &l_Lean_PrettyPrinter_ppExprLegacy___closed__22_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__22);
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
v___x_620_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(v_opts_575_, v___y_603_);
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
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*14, v___y_605_);
lean_ctor_set_uint8(v___x_621_, sizeof(void*)*14 + 1, v_suppressElabErrors_617_);
v___x_622_ = l_Lean_PrettyPrinter_ppExpr(v_e_576_, v___x_585_, v___y_604_, v___x_621_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___x_621_);
lean_dec_ref(v___x_585_);
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
v___x_627_ = lean_st_ref_get(v___y_604_);
lean_dec(v___y_604_);
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
lean_dec(v___y_604_);
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
v___x_644_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__19));
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
v___x_678_ = lean_st_ref_take(v___y_676_);
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
v___x_693_ = lean_st_ref_set(v___y_676_, v___x_692_);
v___y_653_ = v___y_672_;
v___y_654_ = v___y_674_;
v___y_655_ = v___y_675_;
v___y_656_ = v___y_673_;
v___y_657_ = v___y_676_;
goto v___jp_652_;
}
}
}
else
{
v___y_653_ = v___y_672_;
v___y_654_ = v___y_674_;
v___y_655_ = v___y_675_;
v___y_656_ = v___y_673_;
v___y_657_ = v___y_676_;
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
v___x_734_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__23, &l_Lean_PrettyPrinter_ppExprLegacy___closed__23_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__23);
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
v___y_603_ = v___x_733_;
v___y_604_ = v___x_714_;
v___y_605_ = v___x_737_;
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
v___y_672_ = v___x_733_;
v___y_673_ = v___x_736_;
v___y_674_ = v___x_714_;
v___y_675_ = v___x_737_;
v___y_676_ = v___y_713_;
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
v___y_672_ = v___x_733_;
v___y_673_ = v___x_736_;
v___y_674_ = v___x_714_;
v___y_675_ = v___x_737_;
v___y_676_ = v___y_713_;
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppLevel(lean_object* v_l_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = l_Lean_PrettyPrinter_delabLevel(v_l_775_, v___x_781_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_782_);
v___x_784_ = ((lean_object*)(l_Lean_PrettyPrinter_ppLevel___closed__1));
v___x_785_ = l_Lean_PrettyPrinter_ppCategory(v___x_784_, v_a_783_, v_a_778_, v_a_779_);
return v___x_785_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_782_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppLevel___boxed(lean_object* v_l_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_PrettyPrinter_ppLevel(v_l_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic(lean_object* v_stx_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_PrettyPrinter_ppTactic___closed__1));
v___x_809_ = l_Lean_PrettyPrinter_ppCategory(v___x_808_, v_stx_804_, v_a_805_, v_a_806_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic___boxed(lean_object* v_stx_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_PrettyPrinter_ppTactic(v_stx_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object* v_stx_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l_Lean_PrettyPrinter_ppCommand___closed__1));
v___x_823_ = l_Lean_PrettyPrinter_ppCategory(v___x_822_, v_stx_818_, v_a_819_, v_a_820_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand___boxed(lean_object* v_stx_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_PrettyPrinter_ppCommand(v_stx_824_, v_a_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule(lean_object* v_stx_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean_PrettyPrinter_ppModule___closed__0));
v___x_836_ = l_Lean_PrettyPrinter_parenthesize(v___x_835_, v_stx_831_, v_a_832_, v_a_833_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref(v___x_836_);
v___x_838_ = ((lean_object*)(l_Lean_PrettyPrinter_ppModule___closed__1));
v___x_839_ = l_Lean_PrettyPrinter_format(v___x_838_, v_a_837_, v_a_832_, v_a_833_);
return v___x_839_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_836_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_836_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule___boxed(lean_object* v_stx_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_PrettyPrinter_ppModule(v_stx_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
return v_res_852_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_853_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
lean_ctor_set(v___x_858_, 2, v___x_857_);
lean_ctor_set(v___x_858_, 3, v___x_857_);
lean_ctor_set(v___x_858_, 4, v___x_856_);
lean_ctor_set(v___x_858_, 5, v___x_856_);
lean_ctor_set(v___x_858_, 6, v___x_856_);
lean_ctor_set(v___x_858_, 7, v___x_856_);
lean_ctor_set(v___x_858_, 8, v___x_856_);
lean_ctor_set(v___x_858_, 9, v___x_856_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_unsigned_to_nat(32u);
v___x_860_ = lean_mk_empty_array_with_capacity(v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_862_ = ((size_t)5ULL);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_unsigned_to_nat(32u);
v___x_865_ = lean_mk_empty_array_with_capacity(v___x_864_);
v___x_866_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_867_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___x_865_);
lean_ctor_set(v___x_867_, 2, v___x_863_);
lean_ctor_set(v___x_867_, 3, v___x_863_);
lean_ctor_set_usize(v___x_867_, 4, v___x_862_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_868_ = lean_box(1);
v___x_869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_870_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_869_);
lean_ctor_set(v___x_871_, 2, v___x_868_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_893_, lean_object* v_declHint_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; lean_object* v_env_898_; uint8_t v___x_899_; 
v___x_897_ = lean_st_ref_get(v___y_895_);
v_env_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc_ref(v_env_898_);
lean_dec(v___x_897_);
v___x_899_ = l_Lean_Name_isAnonymous(v_declHint_894_);
if (v___x_899_ == 0)
{
uint8_t v_isExporting_900_; 
v_isExporting_900_ = lean_ctor_get_uint8(v_env_898_, sizeof(void*)*8);
if (v_isExporting_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec_ref(v_env_898_);
lean_dec(v_declHint_894_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v_msg_893_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; uint8_t v___x_903_; 
lean_inc_ref(v_env_898_);
v___x_902_ = l_Lean_Environment_setExporting(v_env_898_, v___x_899_);
lean_inc(v_declHint_894_);
lean_inc_ref(v___x_902_);
v___x_903_ = l_Lean_Environment_contains(v___x_902_, v_declHint_894_, v_isExporting_900_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec_ref(v___x_902_);
lean_dec_ref(v_env_898_);
lean_dec(v_declHint_894_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v_msg_893_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v_c_910_; lean_object* v___x_911_; 
v___x_905_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_907_ = l_Lean_Options_empty;
v___x_908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_908_, 0, v___x_902_);
lean_ctor_set(v___x_908_, 1, v___x_905_);
lean_ctor_set(v___x_908_, 2, v___x_906_);
lean_ctor_set(v___x_908_, 3, v___x_907_);
lean_inc(v_declHint_894_);
v___x_909_ = l_Lean_MessageData_ofConstName(v_declHint_894_, v___x_899_);
v_c_910_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_910_, 0, v___x_908_);
lean_ctor_set(v_c_910_, 1, v___x_909_);
v___x_911_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_898_, v_declHint_894_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec_ref(v_env_898_);
lean_dec(v_declHint_894_);
v___x_912_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v_c_910_);
v___x_914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_MessageData_note(v___x_915_);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v_msg_893_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
else
{
lean_object* v_val_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_954_; 
v_val_919_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_954_ == 0)
{
v___x_921_ = v___x_911_;
v_isShared_922_ = v_isSharedCheck_954_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_val_919_);
lean_dec(v___x_911_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_954_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_mod_926_; uint8_t v___x_927_; 
v___x_923_ = lean_box(0);
v___x_924_ = l_Lean_Environment_header(v_env_898_);
lean_dec_ref(v_env_898_);
v___x_925_ = l_Lean_EnvironmentHeader_moduleNames(v___x_924_);
v_mod_926_ = lean_array_get(v___x_923_, v___x_925_, v_val_919_);
lean_dec(v_val_919_);
lean_dec_ref(v___x_925_);
v___x_927_ = l_Lean_isPrivateName(v_declHint_894_);
lean_dec(v_declHint_894_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_928_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v_c_910_);
v___x_930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_MessageData_ofName(v_mod_926_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_MessageData_note(v___x_935_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v_msg_893_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 0);
lean_ctor_set(v___x_921_, 0, v___x_937_);
v___x_939_ = v___x_921_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_941_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v_c_910_);
v___x_943_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l_Lean_MessageData_ofName(v_mod_926_);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Lean_MessageData_note(v___x_948_);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v_msg_893_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 0);
lean_ctor_set(v___x_921_, 0, v___x_950_);
v___x_952_ = v___x_921_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_955_; 
lean_dec_ref(v_env_898_);
lean_dec(v_declHint_894_);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v_msg_893_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_956_, lean_object* v_declHint_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_956_, v_declHint_957_, v___y_958_);
lean_dec(v___y_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_961_, lean_object* v_declHint_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_978_; 
v___x_968_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_961_, v_declHint_962_, v___y_966_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_978_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_973_ = l_Lean_unknownIdentifierMessageTag;
v___x_974_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v_a_969_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_974_);
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_979_, lean_object* v_declHint_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_979_, v_declHint_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; lean_object* v_env_994_; lean_object* v___x_995_; lean_object* v_mctx_996_; lean_object* v_lctx_997_; lean_object* v_options_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_993_ = lean_st_ref_get(v___y_991_);
v_env_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc_ref(v_env_994_);
lean_dec(v___x_993_);
v___x_995_ = lean_st_ref_get(v___y_989_);
v_mctx_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc_ref(v_mctx_996_);
lean_dec(v___x_995_);
v_lctx_997_ = lean_ctor_get(v___y_988_, 2);
v_options_998_ = lean_ctor_get(v___y_990_, 2);
lean_inc_ref(v_options_998_);
lean_inc_ref(v_lctx_997_);
v___x_999_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_999_, 0, v_env_994_);
lean_ctor_set(v___x_999_, 1, v_mctx_996_);
lean_ctor_set(v___x_999_, 2, v_lctx_997_);
lean_ctor_set(v___x_999_, 3, v_options_998_);
v___x_1000_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v_msgData_987_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_ref_1015_; lean_object* v___x_1016_; lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1025_; 
v_ref_1015_ = lean_ctor_get(v___y_1012_, 5);
v___x_1016_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
lean_inc(v_ref_1015_);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_ref_1015_);
lean_ctor_set(v___x_1021_, 1, v_a_1017_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set_tag(v___x_1019_, 1);
lean_ctor_set(v___x_1019_, 0, v___x_1021_);
v___x_1023_ = v___x_1019_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1033_, lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_fileName_1040_; lean_object* v_fileMap_1041_; lean_object* v_options_1042_; lean_object* v_currRecDepth_1043_; lean_object* v_maxRecDepth_1044_; lean_object* v_ref_1045_; lean_object* v_currNamespace_1046_; lean_object* v_openDecls_1047_; lean_object* v_initHeartbeats_1048_; lean_object* v_maxHeartbeats_1049_; lean_object* v_quotContext_1050_; lean_object* v_currMacroScope_1051_; uint8_t v_diag_1052_; lean_object* v_cancelTk_x3f_1053_; uint8_t v_suppressElabErrors_1054_; lean_object* v_inheritedTraceOptions_1055_; lean_object* v_ref_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_fileName_1040_ = lean_ctor_get(v___y_1037_, 0);
v_fileMap_1041_ = lean_ctor_get(v___y_1037_, 1);
v_options_1042_ = lean_ctor_get(v___y_1037_, 2);
v_currRecDepth_1043_ = lean_ctor_get(v___y_1037_, 3);
v_maxRecDepth_1044_ = lean_ctor_get(v___y_1037_, 4);
v_ref_1045_ = lean_ctor_get(v___y_1037_, 5);
v_currNamespace_1046_ = lean_ctor_get(v___y_1037_, 6);
v_openDecls_1047_ = lean_ctor_get(v___y_1037_, 7);
v_initHeartbeats_1048_ = lean_ctor_get(v___y_1037_, 8);
v_maxHeartbeats_1049_ = lean_ctor_get(v___y_1037_, 9);
v_quotContext_1050_ = lean_ctor_get(v___y_1037_, 10);
v_currMacroScope_1051_ = lean_ctor_get(v___y_1037_, 11);
v_diag_1052_ = lean_ctor_get_uint8(v___y_1037_, sizeof(void*)*14);
v_cancelTk_x3f_1053_ = lean_ctor_get(v___y_1037_, 12);
v_suppressElabErrors_1054_ = lean_ctor_get_uint8(v___y_1037_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1055_ = lean_ctor_get(v___y_1037_, 13);
v_ref_1056_ = l_Lean_replaceRef(v_ref_1033_, v_ref_1045_);
lean_inc_ref(v_inheritedTraceOptions_1055_);
lean_inc(v_cancelTk_x3f_1053_);
lean_inc(v_currMacroScope_1051_);
lean_inc(v_quotContext_1050_);
lean_inc(v_maxHeartbeats_1049_);
lean_inc(v_initHeartbeats_1048_);
lean_inc(v_openDecls_1047_);
lean_inc(v_currNamespace_1046_);
lean_inc(v_maxRecDepth_1044_);
lean_inc(v_currRecDepth_1043_);
lean_inc_ref(v_options_1042_);
lean_inc_ref(v_fileMap_1041_);
lean_inc_ref(v_fileName_1040_);
v___x_1057_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1057_, 0, v_fileName_1040_);
lean_ctor_set(v___x_1057_, 1, v_fileMap_1041_);
lean_ctor_set(v___x_1057_, 2, v_options_1042_);
lean_ctor_set(v___x_1057_, 3, v_currRecDepth_1043_);
lean_ctor_set(v___x_1057_, 4, v_maxRecDepth_1044_);
lean_ctor_set(v___x_1057_, 5, v_ref_1056_);
lean_ctor_set(v___x_1057_, 6, v_currNamespace_1046_);
lean_ctor_set(v___x_1057_, 7, v_openDecls_1047_);
lean_ctor_set(v___x_1057_, 8, v_initHeartbeats_1048_);
lean_ctor_set(v___x_1057_, 9, v_maxHeartbeats_1049_);
lean_ctor_set(v___x_1057_, 10, v_quotContext_1050_);
lean_ctor_set(v___x_1057_, 11, v_currMacroScope_1051_);
lean_ctor_set(v___x_1057_, 12, v_cancelTk_x3f_1053_);
lean_ctor_set(v___x_1057_, 13, v_inheritedTraceOptions_1055_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*14, v_diag_1052_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*14 + 1, v_suppressElabErrors_1054_);
v___x_1058_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1034_, v___y_1035_, v___y_1036_, v___x_1057_, v___y_1038_);
lean_dec_ref(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1059_, lean_object* v_msg_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1059_, v_msg_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v_ref_1059_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1067_, lean_object* v_msg_1068_, lean_object* v_declHint_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; lean_object* v_a_1076_; lean_object* v___x_1077_; 
v___x_1075_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1068_, v_declHint_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1067_, v_a_1076_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1078_, lean_object* v_msg_1079_, lean_object* v_declHint_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1078_, v_msg_1079_, v_declHint_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v_ref_1078_);
return v_res_1086_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1093_, lean_object* v_constName_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1100_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1101_ = 0;
lean_inc(v_constName_1094_);
v___x_1102_ = l_Lean_MessageData_ofConstName(v_constName_1094_, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1100_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1093_, v___x_1105_, v_constName_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1107_, lean_object* v_constName_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_1107_, v_constName_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v_ref_1107_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(lean_object* v_constName_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_ref_1121_; lean_object* v___x_1122_; 
v_ref_1121_ = lean_ctor_get(v___y_1118_, 5);
v___x_1122_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_1121_, v_constName_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(lean_object* v_constName_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v_env_1137_; uint8_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1136_ = lean_st_ref_get(v___y_1134_);
v_env_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc_ref(v_env_1137_);
lean_dec(v___x_1136_);
v___x_1138_ = 0;
lean_inc(v_constName_1130_);
v___x_1139_ = l_Lean_Environment_find_x3f(v_env_1137_, v_constName_1130_, v___x_1138_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
return v___x_1140_;
}
else
{
lean_object* v_val_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_constName_1130_);
v_val_1141_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1139_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_val_1141_);
lean_dec(v___x_1139_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 0);
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_val_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0___boxed(lean_object* v_constName_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(v_constName_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object* v_c_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1166_; 
lean_inc(v_c_1160_);
v___x_1166_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(v_c_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1228_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1228_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1228_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_options_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_options_1171_ = lean_ctor_get(v_a_1163_, 2);
v___x_1172_ = l_Lean_ConstantInfo_levelParams(v_a_1167_);
v___x_1173_ = lean_box(0);
v___x_1174_ = l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(v___x_1172_, v___x_1173_);
v___x_1175_ = l_Lean_Expr_const___override(v_c_1160_, v___x_1174_);
v___x_1176_ = l_Lean_pp_raw;
v___x_1177_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_options_1171_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_del_object(v___x_1169_);
lean_dec(v_a_1167_);
v___x_1178_ = lean_box(1);
v___x_1179_ = ((lean_object*)(l_Lean_PrettyPrinter_ppSignature___closed__0));
v___x_1180_ = l_Lean_PrettyPrinter_delabCore___redArg(v___x_1175_, v___x_1178_, v___x_1179_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1207_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref(v___x_1180_);
v_fst_1182_ = lean_ctor_get(v_a_1181_, 0);
v_snd_1183_ = lean_ctor_get(v_a_1181_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_a_1181_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1185_ = v_a_1181_;
v_isShared_1186_ = v_isSharedCheck_1207_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snd_1183_);
lean_inc(v_fst_1182_);
lean_dec(v_a_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1207_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_PrettyPrinter_ppTerm(v_fst_1182_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1198_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1198_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1198_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_a_1188_);
v___x_1193_ = v___x_1185_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1188_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_snd_1183_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1195_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1193_);
v___x_1195_ = v___x_1190_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_del_object(v___x_1185_);
lean_dec(v_snd_1183_);
v_a_1199_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1187_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1187_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
v_a_1208_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1180_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1180_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1216_ = lean_expr_dbg_to_string(v___x_1175_);
lean_dec_ref(v___x_1175_);
v___x_1217_ = ((lean_object*)(l_Lean_PrettyPrinter_ppSignature___closed__1));
v___x_1218_ = lean_string_append(v___x_1216_, v___x_1217_);
v___x_1219_ = l_Lean_ConstantInfo_type(v_a_1167_);
lean_dec(v_a_1167_);
v___x_1220_ = lean_expr_dbg_to_string(v___x_1219_);
lean_dec_ref(v___x_1219_);
v___x_1221_ = lean_string_append(v___x_1218_, v___x_1220_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
v___x_1223_ = lean_box(1);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1224_);
v___x_1226_ = v___x_1169_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_c_1160_);
v_a_1229_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1166_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1166_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature___boxed(lean_object* v_c_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_PrettyPrinter_ppSignature(v_c_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(lean_object* v_00_u03b1_1244_, lean_object* v_constName_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1252_, lean_object* v_constName_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(v_00_u03b1_1252_, v_constName_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1260_, lean_object* v_ref_1261_, lean_object* v_constName_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_1261_, v_constName_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1269_, lean_object* v_ref_1270_, lean_object* v_constName_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(v_00_u03b1_1269_, v_ref_1270_, v_constName_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v_ref_1270_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1278_, lean_object* v_ref_1279_, lean_object* v_msg_1280_, lean_object* v_declHint_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1279_, v_msg_1280_, v_declHint_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1288_, lean_object* v_ref_1289_, lean_object* v_msg_1290_, lean_object* v_declHint_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1288_, v_ref_1289_, v_msg_1290_, v_declHint_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v_ref_1289_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1298_, lean_object* v_declHint_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1298_, v_declHint_1299_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1306_, lean_object* v_declHint_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1306_, v_declHint_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1314_, lean_object* v_ref_1315_, lean_object* v_msg_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1315_, v_msg_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1323_, lean_object* v_ref_1324_, lean_object* v_msg_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1323_, v_ref_1324_, v_msg_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v_ref_1324_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1332_, lean_object* v_msg_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1340_, lean_object* v_msg_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1340_, v_msg_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(lean_object* v_x_1348_){
_start:
{
switch(lean_obj_tag(v_x_1348_))
{
case 3:
{
lean_object* v_a_1349_; 
v_a_1349_ = lean_ctor_get(v_x_1348_, 1);
lean_inc_ref(v_a_1349_);
lean_dec_ref(v_x_1348_);
v_x_1348_ = v_a_1349_;
goto _start;
}
case 4:
{
lean_object* v_a_1351_; lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_a_1351_ = lean_ctor_get(v_x_1348_, 0);
v_a_1352_ = lean_ctor_get(v_x_1348_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v_x_1348_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_inc(v_a_1351_);
lean_dec(v_x_1348_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1351_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
case 5:
{
lean_object* v_a_1361_; lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1370_; 
v_a_1361_ = lean_ctor_get(v_x_1348_, 0);
v_a_1362_ = lean_ctor_get(v_x_1348_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1364_ = v_x_1348_;
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_inc(v_a_1361_);
lean_dec(v_x_1348_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1362_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v___x_1366_);
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1361_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
case 6:
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1379_; 
v_a_1371_ = lean_ctor_get(v_x_1348_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1373_ = v_x_1348_;
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v_x_1348_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1371_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1375_);
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
case 7:
{
lean_object* v_a_1380_; lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1390_; 
v_a_1380_ = lean_ctor_get(v_x_1348_, 0);
v_a_1381_ = lean_ctor_get(v_x_1348_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1383_ = v_x_1348_;
v_isShared_1384_ = v_isSharedCheck_1390_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_inc(v_a_1380_);
lean_dec(v_x_1348_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1390_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1385_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1380_);
v___x_1386_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1381_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1386_);
lean_ctor_set(v___x_1383_, 0, v___x_1385_);
v___x_1388_ = v___x_1383_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
case 8:
{
lean_object* v_a_1391_; lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
v_a_1391_ = lean_ctor_get(v_x_1348_, 0);
v_a_1392_ = lean_ctor_get(v_x_1348_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1394_ = v_x_1348_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_inc(v_a_1391_);
lean_dec(v_x_1348_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1392_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1391_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
case 9:
{
lean_object* v_data_1401_; lean_object* v_msg_1402_; lean_object* v_children_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1414_; 
v_data_1401_ = lean_ctor_get(v_x_1348_, 0);
v_msg_1402_ = lean_ctor_get(v_x_1348_, 1);
v_children_1403_ = lean_ctor_get(v_x_1348_, 2);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1405_ = v_x_1348_;
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_children_1403_);
lean_inc(v_msg_1402_);
lean_inc(v_data_1401_);
lean_dec(v_x_1348_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; size_t v_sz_1408_; size_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1407_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1402_);
v_sz_1408_ = lean_array_size(v_children_1403_);
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(v_sz_1408_, v___x_1409_, v_children_1403_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 2, v___x_1410_);
lean_ctor_set(v___x_1405_, 1, v___x_1407_);
v___x_1412_ = v___x_1405_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_data_1401_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
default: 
{
return v_x_1348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(size_t v_sz_1415_, size_t v_i_1416_, lean_object* v_bs_1417_){
_start:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_usize_dec_lt(v_i_1416_, v_sz_1415_);
if (v___x_1418_ == 0)
{
return v_bs_1417_;
}
else
{
lean_object* v_v_1419_; lean_object* v___x_1420_; lean_object* v_bs_x27_1421_; lean_object* v___x_1422_; size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v_v_1419_ = lean_array_uget(v_bs_1417_, v_i_1416_);
v___x_1420_ = lean_unsigned_to_nat(0u);
v_bs_x27_1421_ = lean_array_uset(v_bs_1417_, v_i_1416_, v___x_1420_);
v___x_1422_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_v_1419_);
v___x_1423_ = ((size_t)1ULL);
v___x_1424_ = lean_usize_add(v_i_1416_, v___x_1423_);
v___x_1425_ = lean_array_uset(v_bs_x27_1421_, v_i_1416_, v___x_1422_);
v_i_1416_ = v___x_1424_;
v_bs_1417_ = v___x_1425_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0___boxed(lean_object* v_sz_1427_, lean_object* v_i_1428_, lean_object* v_bs_1429_){
_start:
{
size_t v_sz_boxed_1430_; size_t v_i_boxed_1431_; lean_object* v_res_1432_; 
v_sz_boxed_1430_ = lean_unbox_usize(v_sz_1427_);
lean_dec(v_sz_1427_);
v_i_boxed_1431_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_res_1432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(v_sz_boxed_1430_, v_i_boxed_1431_, v_bs_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0(lean_object* v_throw_1433_, lean_object* v_x_1434_){
_start:
{
if (lean_obj_tag(v_x_1434_) == 0)
{
lean_object* v_ref_1435_; lean_object* v_msg_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1445_; 
v_ref_1435_ = lean_ctor_get(v_x_1434_, 0);
v_msg_1436_ = lean_ctor_get(v_x_1434_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_x_1434_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1438_ = v_x_1434_;
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_msg_1436_);
lean_inc(v_ref_1435_);
lean_dec(v_x_1434_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1445_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1436_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 1, v___x_1440_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_ref_1435_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_apply_2(v_throw_1433_, lean_box(0), v___x_1442_);
return v___x_1443_;
}
}
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_apply_2(v_throw_1433_, lean_box(0), v_x_1434_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(lean_object* v_inst_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v_throw_1449_; lean_object* v_tryCatch_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; 
v_throw_1449_ = lean_ctor_get(v_inst_1447_, 0);
lean_inc(v_throw_1449_);
v_tryCatch_1450_ = lean_ctor_get(v_inst_1447_, 1);
lean_inc(v_tryCatch_1450_);
lean_dec_ref(v_inst_1447_);
v___f_1451_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1451_, 0, v_throw_1449_);
v___x_1452_ = lean_apply_3(v_tryCatch_1450_, lean_box(0), v_x_1448_, v___f_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(lean_object* v_00_u03b1_1453_, lean_object* v_m_1454_, lean_object* v_inst_1455_, lean_object* v_x_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(v_inst_1455_, v_x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1461_);
lean_inc(v___y_1460_);
lean_inc_ref(v___y_1459_);
v___x_1464_ = lean_apply_5(v_x_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, lean_box(0));
if (lean_obj_tag(v___x_1464_) == 0)
{
return v___x_1464_;
}
else
{
lean_object* v_a_1465_; uint8_t v___y_1467_; uint8_t v___x_1486_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
v___x_1486_ = l_Lean_Exception_isInterrupt(v_a_1465_);
if (v___x_1486_ == 0)
{
uint8_t v___x_1487_; 
lean_inc(v_a_1465_);
v___x_1487_ = l_Lean_Exception_isRuntime(v_a_1465_);
v___y_1467_ = v___x_1487_;
goto v___jp_1466_;
}
else
{
v___y_1467_ = v___x_1486_;
goto v___jp_1466_;
}
v___jp_1466_:
{
if (v___y_1467_ == 0)
{
if (lean_obj_tag(v_a_1465_) == 0)
{
lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1484_; 
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v___x_1464_, 0);
lean_dec(v_unused_1485_);
v___x_1469_ = v___x_1464_;
v_isShared_1470_ = v_isSharedCheck_1484_;
goto v_resetjp_1468_;
}
else
{
lean_dec(v___x_1464_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1484_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_ref_1471_; lean_object* v_msg_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1483_; 
v_ref_1471_ = lean_ctor_get(v_a_1465_, 0);
v_msg_1472_ = lean_ctor_get(v_a_1465_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_a_1465_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1474_ = v_a_1465_;
v_isShared_1475_ = v_isSharedCheck_1483_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_msg_1472_);
lean_inc(v_ref_1471_);
lean_dec(v_a_1465_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1483_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1476_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1472_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1476_);
v___x_1478_ = v___x_1474_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_ref_1471_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1478_);
v___x_1480_ = v___x_1469_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
else
{
lean_dec(v_a_1465_);
return v___x_1464_;
}
}
else
{
lean_dec(v_a_1465_);
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(v_x_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1495_, lean_object* v_x_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(v_x_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1503_, lean_object* v_x_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0(v_00_u03b1_1503_, v_x_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
lean_inc(v___y_1513_);
lean_inc_ref(v___y_1512_);
v___x_1515_ = lean_apply_3(v_x_1511_, v___y_1512_, v___y_1513_, lean_box(0));
if (lean_obj_tag(v___x_1515_) == 0)
{
return v___x_1515_;
}
else
{
lean_object* v_a_1516_; uint8_t v___y_1518_; uint8_t v___x_1537_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
v___x_1537_ = l_Lean_Exception_isInterrupt(v_a_1516_);
if (v___x_1537_ == 0)
{
uint8_t v___x_1538_; 
lean_inc(v_a_1516_);
v___x_1538_ = l_Lean_Exception_isRuntime(v_a_1516_);
v___y_1518_ = v___x_1538_;
goto v___jp_1517_;
}
else
{
v___y_1518_ = v___x_1537_;
goto v___jp_1517_;
}
v___jp_1517_:
{
if (v___y_1518_ == 0)
{
if (lean_obj_tag(v_a_1516_) == 0)
{
lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1535_; 
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v___x_1515_, 0);
lean_dec(v_unused_1536_);
v___x_1520_ = v___x_1515_;
v_isShared_1521_ = v_isSharedCheck_1535_;
goto v_resetjp_1519_;
}
else
{
lean_dec(v___x_1515_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1535_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_ref_1522_; lean_object* v_msg_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1534_; 
v_ref_1522_ = lean_ctor_get(v_a_1516_, 0);
v_msg_1523_ = lean_ctor_get(v_a_1516_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_a_1516_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1525_ = v_a_1516_;
v_isShared_1526_ = v_isSharedCheck_1534_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_msg_1523_);
lean_inc(v_ref_1522_);
lean_dec(v_a_1516_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1534_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
v___x_1527_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1523_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 1, v___x_1527_);
v___x_1529_ = v___x_1525_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_ref_1522_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1531_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1529_);
v___x_1531_ = v___x_1520_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
else
{
lean_dec(v_a_1516_);
return v___x_1515_;
}
}
else
{
lean_dec(v_a_1516_);
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(v_x_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1544_, lean_object* v_x_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(v_x_1545_, v___y_1546_, v___y_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1550_, lean_object* v_x_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1(v_00_u03b1_1550_, v_x_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object* v_ctx_1557_, lean_object* v_e_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1560_ = lean_box(1);
v___x_1561_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_));
v___x_1562_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___boxed), 8, 3);
lean_closure_set(v___x_1562_, 0, v_e_1558_);
lean_closure_set(v___x_1562_, 1, v___x_1560_);
lean_closure_set(v___x_1562_, 2, v___x_1561_);
v___x_1563_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1563_, 0, lean_box(0));
lean_closure_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1557_, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_ctx_1565_, lean_object* v_e_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_1565_, v_e_1566_);
lean_dec_ref(v_ctx_1565_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object* v_ctx_1569_, lean_object* v_n_1570_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1572_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___boxed), 6, 1);
lean_closure_set(v___x_1572_, 0, v_n_1570_);
v___x_1573_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1573_, 0, lean_box(0));
lean_closure_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1569_, v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_ctx_1575_, lean_object* v_n_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_1575_, v_n_1576_);
lean_dec_ref(v_ctx_1575_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object* v_ctx_1579_, lean_object* v_l_1580_){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppLevel___boxed), 6, 1);
lean_closure_set(v___x_1582_, 0, v_l_1580_);
v___x_1583_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1583_, 0, lean_box(0));
lean_closure_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1579_, v___x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_ctx_1585_, lean_object* v_l_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_1585_, v_l_1586_);
lean_dec_ref(v_ctx_1585_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object* v_ctx_1589_, lean_object* v_mvarId_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal___boxed), 6, 1);
lean_closure_set(v___x_1592_, 0, v_mvarId_1590_);
v___x_1593_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1593_, 0, lean_box(0));
lean_closure_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1589_, v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_ctx_1595_, lean_object* v_mvarId_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_1595_, v_mvarId_1596_);
lean_dec_ref(v_ctx_1595_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object* v_ctx_1599_, lean_object* v_stx_1600_){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTerm___boxed), 4, 1);
lean_closure_set(v___x_1602_, 0, v_stx_1600_);
v___x_1603_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___boxed), 5, 2);
lean_closure_set(v___x_1603_, 0, lean_box(0));
lean_closure_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = l_Lean_PPContext_runCoreM___redArg(v_ctx_1599_, v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_ctx_1605_, lean_object* v_stx_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_1605_, v_stx_1606_);
lean_dec_ref(v_ctx_1605_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1621_ = l_Lean_ppFnsRef;
v___x_1622_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_));
v___x_1623_ = lean_st_ref_set(v___x_1621_, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_a_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_();
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_));
v___x_1678_ = 0;
v___x_1679_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_));
v___x_1680_ = l_Lean_registerTraceClass(v___x_1677_, v___x_1678_, v___x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2____boxed(lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_();
return v_res_1682_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1686_ = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
v___x_1687_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1688_ = ((lean_object*)(l_Lean_PrettyPrinter_registerParserCompilers___closed__1));
v___x_1689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v___x_1687_);
lean_ctor_set(v___x_1689_, 2, v___x_1686_);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1693_ = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
v___x_1694_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1695_ = ((lean_object*)(l_Lean_PrettyPrinter_registerParserCompilers___closed__4));
v___x_1696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v___x_1694_);
lean_ctor_set(v___x_1696_, 2, v___x_1693_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers(){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = lean_obj_once(&l_Lean_PrettyPrinter_registerParserCompilers___closed__2, &l_Lean_PrettyPrinter_registerParserCompilers___closed__2_once, _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2);
v___x_1699_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v___x_1698_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_dec_ref(v___x_1699_);
v___x_1700_ = lean_obj_once(&l_Lean_PrettyPrinter_registerParserCompilers___closed__5, &l_Lean_PrettyPrinter_registerParserCompilers___closed__5_once, _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5);
v___x_1701_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v___x_1700_);
return v___x_1701_;
}
else
{
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers___boxed(lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_PrettyPrinter_registerParserCompilers();
return v_res_1703_;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0(lean_object* v_fmt_1710_, lean_object* v_ctx_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1711_, v_fmt_1710_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1735_; 
v_a_1722_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1724_ = v___x_1713_;
v_isShared_1725_ = v_isSharedCheck_1735_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1713_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1735_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1726_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1, &l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1);
v___x_1727_ = lean_io_error_to_string(v_a_1722_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set_tag(v___x_1724_, 3);
lean_ctor_set(v___x_1724_, 0, v___x_1727_);
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1730_ = l_Lean_MessageData_ofFormat(v___x_1729_);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1726_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3, &l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
return v___x_1733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed(lean_object* v_fmt_1736_, lean_object* v_ctx_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_MessageData_ofFormatWithInfosM___lam__0(v_fmt_1736_, v_ctx_1737_);
lean_dec_ref(v_ctx_1737_);
return v_res_1739_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofFormatWithInfosM___lam__1(lean_object* v_x_1740_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = 0;
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed(lean_object* v_x_1742_){
_start:
{
uint8_t v_res_1743_; lean_object* v_r_1744_; 
v_res_1743_ = l_Lean_MessageData_ofFormatWithInfosM___lam__1(v_x_1742_);
lean_dec_ref(v_x_1742_);
v_r_1744_ = lean_box(v_res_1743_);
return v_r_1744_;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1));
v___x_1749_ = l_Lean_MessageData_ofFormat(v___x_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2(lean_object* v_x_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2, &l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed(lean_object* v_x_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_MessageData_ofFormatWithInfosM___lam__2(v_x_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM(lean_object* v_fmt_1758_){
_start:
{
lean_object* v___f_1759_; lean_object* v___f_1760_; lean_object* v___f_1761_; lean_object* v___x_1762_; 
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1759_, 0, v_fmt_1758_);
v___f_1760_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__0));
v___f_1761_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__1));
v___x_1762_ = l_Lean_MessageData_lazy(v___f_1759_, v___f_1760_, v___f_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_ofConst_spec__0(lean_object* v___x_1763_, lean_object* v_msg_1764_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_panic_fn_borrowed(v___x_1763_, v_msg_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_ofConst_spec__0___boxed(lean_object* v___x_1766_, lean_object* v_msg_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_panic___at___00Lean_MessageData_ofConst_spec__0(v___x_1766_, v_msg_1767_);
lean_dec_ref(v___x_1766_);
return v_res_1768_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__1(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__0));
v___x_1771_ = l_Lean_stringToMessageData(v___x_1770_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__2(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_box(1);
v___x_1773_ = l_Lean_MessageData_ofFormat(v___x_1772_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__3(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__2, &l_Lean_MessageData_ofConst___closed__2_once, _init_l_Lean_MessageData_ofConst___closed__2);
v___x_1775_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__1, &l_Lean_MessageData_ofConst___closed__1_once, _init_l_Lean_MessageData_ofConst___closed__1);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___x_1774_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__7(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1780_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__6));
v___x_1781_ = lean_unsigned_to_nat(4u);
v___x_1782_ = lean_unsigned_to_nat(156u);
v___x_1783_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__5));
v___x_1784_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__4));
v___x_1785_ = l_mkPanicMessageWithDecl(v___x_1784_, v___x_1783_, v___x_1782_, v___x_1781_, v___x_1780_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConst(lean_object* v_e_1786_){
_start:
{
uint8_t v___x_1787_; 
v___x_1787_ = l_Lean_Expr_isConst(v_e_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1788_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__3, &l_Lean_MessageData_ofConst___closed__3_once, _init_l_Lean_MessageData_ofConst___closed__3);
v___x_1789_ = l_Lean_MessageData_ofExpr(v_e_1786_);
v___x_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__7, &l_Lean_MessageData_ofConst___closed__7_once, _init_l_Lean_MessageData_ofConst___closed__7);
v___x_1792_ = lean_panic_fn_borrowed(v___x_1790_, v___x_1791_);
lean_dec_ref(v___x_1790_);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v_delab_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1793_ = ((lean_object*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1));
v___x_1794_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1794_, 0, v___x_1787_);
v___x_1795_ = ((lean_object*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3));
v_delab_1796_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed), 11, 4);
lean_closure_set(v_delab_1796_, 0, lean_box(0));
lean_closure_set(v_delab_1796_, 1, v___x_1793_);
lean_closure_set(v_delab_1796_, 2, v___x_1794_);
lean_closure_set(v_delab_1796_, 3, v___x_1795_);
v___x_1797_ = lean_box(1);
v___x_1798_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___boxed), 8, 3);
lean_closure_set(v___x_1798_, 0, v_e_1786_);
lean_closure_set(v___x_1798_, 1, v___x_1797_);
lean_closure_set(v___x_1798_, 2, v_delab_1796_);
v___x_1799_ = l_Lean_MessageData_ofFormatWithInfosM(v___x_1798_);
return v___x_1799_;
}
}
}
static lean_object* _init_l_Lean_MessageData_signature___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lean_MessageData_signature___lam__0___closed__0));
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0(lean_object* v_c_1803_, lean_object* v_ctx_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_inc(v_c_1803_);
v___x_1806_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppSignature___boxed), 6, 1);
lean_closure_set(v___x_1806_, 0, v_c_1803_);
v___x_1807_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1804_, v___x_1806_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v_c_1803_);
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1833_; 
v_a_1816_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1818_ = v___x_1807_;
v_isShared_1819_ = v_isSharedCheck_1833_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1807_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1833_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1820_ = lean_obj_once(&l_Lean_MessageData_signature___lam__0___closed__1, &l_Lean_MessageData_signature___lam__0___closed__1_once, _init_l_Lean_MessageData_signature___lam__0___closed__1);
v___x_1821_ = lean_io_error_to_string(v_a_1816_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set_tag(v___x_1818_, 3);
lean_ctor_set(v___x_1818_, 0, v___x_1821_);
v___x_1823_ = v___x_1818_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1824_ = l_Lean_MessageData_ofFormat(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1820_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3, &l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3);
v___x_1827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1825_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__2, &l_Lean_MessageData_ofConst___closed__2_once, _init_l_Lean_MessageData_ofConst___closed__2);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = l_Lean_MessageData_ofName(v_c_1803_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
return v___x_1831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0___boxed(lean_object* v_c_1834_, lean_object* v_ctx_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_MessageData_signature___lam__0(v_c_1834_, v_ctx_1835_);
lean_dec_ref(v_ctx_1835_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature(lean_object* v_c_1838_){
_start:
{
lean_object* v___f_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; 
v___f_1839_ = lean_alloc_closure((void*)(l_Lean_MessageData_signature___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1839_, 0, v_c_1838_);
v___f_1840_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__0));
v___f_1841_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__1));
v___x_1842_ = l_Lean_MessageData_lazy(v___f_1839_, v___f_1840_, v___f_1841_);
return v___x_1842_;
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
res = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_pp_exprSizes = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_pp_exprSizes);
lean_dec_ref(res);
res = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_();
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
