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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* lean_mk_io_user_error(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
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
static const lean_string_object l_Lean_PrettyPrinter_ppExprLegacy___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "internal exception "};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__19 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__19_value;
static const lean_string_object l_Lean_PrettyPrinter_ppExprLegacy___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception #"};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__20 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__20_value;
static const lean_string_object l_Lean_PrettyPrinter_ppExprLegacy___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " (unknown)"};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__21 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__21_value;
static const lean_string_object l_Lean_PrettyPrinter_ppExprLegacy___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<PrettyPrinter>"};
static const lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__22 = (const lean_object*)&l_Lean_PrettyPrinter_ppExprLegacy___closed__22_value;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__23;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_PrettyPrinter_ppExprLegacy___closed__24;
static lean_once_cell_t l_Lean_PrettyPrinter_ppExprLegacy___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__25;
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
lean_dec_ref_known(v___x_11_, 1);
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
lean_dec_ref_known(v___x_94_, 1);
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
lean_dec_ref_known(v___x_199_, 1);
if (lean_obj_tag(v_val_201_) == 1)
{
uint8_t v_v_202_; 
v_v_202_ = lean_ctor_get_uint8(v_val_201_, 0);
lean_dec_ref_known(v_val_201_, 0);
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
lean_dec_ref_known(v___x_226_, 1);
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
lean_dec_ref_known(v___x_323_, 1);
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
lean_dec_ref_known(v___x_341_, 1);
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
lean_dec_ref_known(v___x_369_, 1);
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
lean_dec_ref_known(v___x_449_, 1);
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
v___x_459_ = l_Lean_mkIdent(v_constName_440_);
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
lean_dec_ref_known(v___x_502_, 1);
if (lean_obj_tag(v_val_503_) == 3)
{
lean_object* v_v_504_; 
v_v_504_ = lean_ctor_get(v_val_503_, 0);
lean_inc(v_v_504_);
lean_dec_ref_known(v_val_503_, 1);
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
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__23(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = l_Lean_Options_empty;
v___x_567_ = l_Lean_Core_getMaxHeartbeats(v___x_566_);
return v___x_567_;
}
}
static uint8_t _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__24(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_568_ = l_Lean_diagnostics;
v___x_569_ = l_Lean_Options_empty;
v___x_570_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v___x_569_, v___x_568_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__25(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = l_Lean_maxRecDepth;
v___x_572_ = l_Lean_Options_empty;
v___x_573_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(v___x_572_, v___x_571_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy(lean_object* v_env_574_, lean_object* v_mctx_575_, lean_object* v_lctx_576_, lean_object* v_opts_577_, lean_object* v_e_578_){
_start:
{
lean_object* v_a_581_; lean_object* v___x_584_; uint8_t v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; uint8_t v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; uint8_t v___y_676_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_env_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___y_712_; lean_object* v___y_713_; uint8_t v___y_744_; uint8_t v___x_765_; 
v___x_584_ = lean_box(1);
v___x_585_ = 0;
v___x_586_ = 1;
v___x_587_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__2, &l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__3));
v___x_590_ = lean_box(0);
v___x_591_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_591_, 0, v___x_587_);
lean_ctor_set(v___x_591_, 1, v___x_584_);
lean_ctor_set(v___x_591_, 2, v_lctx_576_);
lean_ctor_set(v___x_591_, 3, v___x_589_);
lean_ctor_set(v___x_591_, 4, v___x_590_);
lean_ctor_set(v___x_591_, 5, v___x_588_);
lean_ctor_set(v___x_591_, 6, v___x_590_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*7, v___x_585_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*7 + 1, v___x_585_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*7 + 2, v___x_585_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*7 + 3, v___x_586_);
v___x_592_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__6, &l_Lean_PrettyPrinter_ppExprLegacy___closed__6_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6);
v___x_593_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__8, &l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8);
v___x_594_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__9, &l_Lean_PrettyPrinter_ppExprLegacy___closed__9_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9);
v___x_595_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__10, &l_Lean_PrettyPrinter_ppExprLegacy___closed__10_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__10);
v___x_596_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__11, &l_Lean_PrettyPrinter_ppExprLegacy___closed__11_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__11);
v___x_597_ = lean_io_get_num_heartbeats();
v___x_598_ = l_Lean_firstFrontendMacroScope;
v___x_599_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__12, &l_Lean_PrettyPrinter_ppExprLegacy___closed__12_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__12);
v___x_600_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__15));
v___x_601_ = lean_box(0);
v___x_602_ = lean_box(0);
v___x_603_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__16));
v___x_604_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__17, &l_Lean_PrettyPrinter_ppExprLegacy___closed__17_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__17);
v___x_605_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__18, &l_Lean_PrettyPrinter_ppExprLegacy___closed__18_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__18);
v___x_606_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_606_, 0, v_env_574_);
lean_ctor_set(v___x_606_, 1, v___x_599_);
lean_ctor_set(v___x_606_, 2, v___x_600_);
lean_ctor_set(v___x_606_, 3, v___x_603_);
lean_ctor_set(v___x_606_, 4, v___x_604_);
lean_ctor_set(v___x_606_, 5, v___x_595_);
lean_ctor_set(v___x_606_, 6, v___x_596_);
lean_ctor_set(v___x_606_, 7, v___x_605_);
lean_ctor_set(v___x_606_, 8, v___x_589_);
v___x_607_ = lean_st_mk_ref(v___x_606_);
v___x_697_ = l_Lean_inheritedTraceOptions;
v___x_698_ = lean_st_ref_get(v___x_697_);
v___x_699_ = lean_st_ref_get(v___x_607_);
v___x_700_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__22));
v___x_701_ = l_Lean_instInhabitedFileMap_default;
v___x_702_ = l_Lean_Options_empty;
v___x_703_ = lean_unsigned_to_nat(1000u);
v___x_704_ = lean_box(0);
v___x_705_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__23, &l_Lean_PrettyPrinter_ppExprLegacy___closed__23_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__23);
v___x_706_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_706_, 0, v___x_700_);
lean_ctor_set(v___x_706_, 1, v___x_701_);
lean_ctor_set(v___x_706_, 2, v___x_702_);
lean_ctor_set(v___x_706_, 3, v___x_588_);
lean_ctor_set(v___x_706_, 4, v___x_703_);
lean_ctor_set(v___x_706_, 5, v___x_704_);
lean_ctor_set(v___x_706_, 6, v___x_601_);
lean_ctor_set(v___x_706_, 7, v___x_602_);
lean_ctor_set(v___x_706_, 8, v___x_597_);
lean_ctor_set(v___x_706_, 9, v___x_705_);
lean_ctor_set(v___x_706_, 10, v___x_601_);
lean_ctor_set(v___x_706_, 11, v___x_598_);
lean_ctor_set(v___x_706_, 12, v___x_590_);
lean_ctor_set(v___x_706_, 13, v___x_698_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*14, v___x_585_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*14 + 1, v___x_585_);
v_env_707_ = lean_ctor_get(v___x_699_, 0);
lean_inc_ref(v_env_707_);
lean_dec(v___x_699_);
v___x_708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_708_, 0, v_mctx_575_);
lean_ctor_set(v___x_708_, 1, v___x_592_);
lean_ctor_set(v___x_708_, 2, v___x_584_);
lean_ctor_set(v___x_708_, 3, v___x_593_);
lean_ctor_set(v___x_708_, 4, v___x_594_);
v___x_709_ = l_Lean_diagnostics;
v___x_710_ = lean_uint8_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__24, &l_Lean_PrettyPrinter_ppExprLegacy___closed__24_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__24);
v___x_765_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_707_);
lean_dec_ref(v_env_707_);
if (v___x_765_ == 0)
{
if (v___x_710_ == 0)
{
v___y_744_ = v___x_586_;
goto v___jp_743_;
}
else
{
v___y_744_ = v___x_765_;
goto v___jp_743_;
}
}
else
{
v___y_744_ = v___x_710_;
goto v___jp_743_;
}
v___jp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_mk_io_user_error(v_a_581_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
v___jp_608_:
{
lean_object* v_fileName_614_; lean_object* v_fileMap_615_; lean_object* v_currRecDepth_616_; lean_object* v_ref_617_; lean_object* v_currNamespace_618_; lean_object* v_openDecls_619_; lean_object* v_initHeartbeats_620_; lean_object* v_maxHeartbeats_621_; lean_object* v_quotContext_622_; lean_object* v_currMacroScope_623_; lean_object* v_cancelTk_x3f_624_; uint8_t v_suppressElabErrors_625_; lean_object* v_inheritedTraceOptions_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_667_; 
v_fileName_614_ = lean_ctor_get(v___y_612_, 0);
v_fileMap_615_ = lean_ctor_get(v___y_612_, 1);
v_currRecDepth_616_ = lean_ctor_get(v___y_612_, 3);
v_ref_617_ = lean_ctor_get(v___y_612_, 5);
v_currNamespace_618_ = lean_ctor_get(v___y_612_, 6);
v_openDecls_619_ = lean_ctor_get(v___y_612_, 7);
v_initHeartbeats_620_ = lean_ctor_get(v___y_612_, 8);
v_maxHeartbeats_621_ = lean_ctor_get(v___y_612_, 9);
v_quotContext_622_ = lean_ctor_get(v___y_612_, 10);
v_currMacroScope_623_ = lean_ctor_get(v___y_612_, 11);
v_cancelTk_x3f_624_ = lean_ctor_get(v___y_612_, 12);
v_suppressElabErrors_625_ = lean_ctor_get_uint8(v___y_612_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_626_ = lean_ctor_get(v___y_612_, 13);
v_isSharedCheck_667_ = !lean_is_exclusive(v___y_612_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; lean_object* v_unused_669_; 
v_unused_668_ = lean_ctor_get(v___y_612_, 4);
lean_dec(v_unused_668_);
v_unused_669_ = lean_ctor_get(v___y_612_, 2);
lean_dec(v_unused_669_);
v___x_628_ = v___y_612_;
v_isShared_629_ = v_isSharedCheck_667_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_inheritedTraceOptions_626_);
lean_inc(v_cancelTk_x3f_624_);
lean_inc(v_currMacroScope_623_);
lean_inc(v_quotContext_622_);
lean_inc(v_maxHeartbeats_621_);
lean_inc(v_initHeartbeats_620_);
lean_inc(v_openDecls_619_);
lean_inc(v_currNamespace_618_);
lean_inc(v_ref_617_);
lean_inc(v_currRecDepth_616_);
lean_inc(v_fileMap_615_);
lean_inc(v_fileName_614_);
lean_dec(v___y_612_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_667_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(v_opts_577_, v___y_611_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 4, v___x_630_);
lean_ctor_set(v___x_628_, 2, v_opts_577_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_fileName_614_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_fileMap_615_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_opts_577_);
lean_ctor_set(v_reuseFailAlloc_666_, 3, v_currRecDepth_616_);
lean_ctor_set(v_reuseFailAlloc_666_, 4, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_666_, 5, v_ref_617_);
lean_ctor_set(v_reuseFailAlloc_666_, 6, v_currNamespace_618_);
lean_ctor_set(v_reuseFailAlloc_666_, 7, v_openDecls_619_);
lean_ctor_set(v_reuseFailAlloc_666_, 8, v_initHeartbeats_620_);
lean_ctor_set(v_reuseFailAlloc_666_, 9, v_maxHeartbeats_621_);
lean_ctor_set(v_reuseFailAlloc_666_, 10, v_quotContext_622_);
lean_ctor_set(v_reuseFailAlloc_666_, 11, v_currMacroScope_623_);
lean_ctor_set(v_reuseFailAlloc_666_, 12, v_cancelTk_x3f_624_);
lean_ctor_set(v_reuseFailAlloc_666_, 13, v_inheritedTraceOptions_626_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*14 + 1, v_suppressElabErrors_625_);
v___x_632_ = v_reuseFailAlloc_666_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; 
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*14, v___y_609_);
v___x_633_ = l_Lean_PrettyPrinter_ppExpr(v_e_578_, v___x_591_, v___y_610_, v___x_632_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___x_632_);
lean_dec_ref_known(v___x_591_, 7);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_643_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_643_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_638_ = lean_st_ref_get(v___y_610_);
lean_dec(v___y_610_);
lean_dec(v___x_638_);
v___x_639_ = lean_st_ref_get(v___x_607_);
lean_dec(v___x_607_);
lean_dec(v___x_639_);
if (v_isShared_637_ == 0)
{
v___x_641_ = v___x_636_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_634_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_665_; 
lean_dec(v___y_610_);
lean_dec(v___x_607_);
v_a_644_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_665_ == 0)
{
v___x_646_ = v___x_633_;
v_isShared_647_ = v_isSharedCheck_665_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_633_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_665_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
if (lean_obj_tag(v_a_644_) == 0)
{
lean_object* v_msg_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v_msg_648_ = lean_ctor_get(v_a_644_, 1);
lean_inc_ref(v_msg_648_);
lean_dec_ref_known(v_a_644_, 2);
v___x_649_ = l_Lean_MessageData_toString(v_msg_648_);
v___x_650_ = lean_mk_io_user_error(v___x_649_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_650_);
v___x_652_ = v___x_646_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
lean_object* v_id_654_; lean_object* v___x_655_; 
lean_del_object(v___x_646_);
v_id_654_ = lean_ctor_get(v_a_644_, 0);
lean_inc(v_id_654_);
lean_dec_ref_known(v_a_644_, 2);
v___x_655_ = l_Lean_InternalExceptionId_getName(v_id_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v_id_654_);
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__19));
v___x_658_ = l_Lean_Name_toString(v_a_656_, v___x_586_);
v___x_659_ = lean_string_append(v___x_657_, v___x_658_);
lean_dec_ref(v___x_658_);
v_a_581_ = v___x_659_;
goto v___jp_580_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec_ref_known(v___x_655_, 1);
v___x_660_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__20));
v___x_661_ = l_Nat_reprFast(v_id_654_);
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
lean_dec_ref(v___x_661_);
v___x_663_ = ((lean_object*)(l_Lean_PrettyPrinter_ppExprLegacy___closed__21));
v___x_664_ = lean_string_append(v___x_662_, v___x_663_);
v_a_581_ = v___x_664_;
goto v___jp_580_;
}
}
}
}
}
}
}
v___jp_670_:
{
uint8_t v___x_677_; 
v___x_677_ = lean_bool_not(v___y_676_);
if (v___x_677_ == 0)
{
v___y_609_ = v___y_671_;
v___y_610_ = v___y_674_;
v___y_611_ = v___y_673_;
v___y_612_ = v___y_672_;
v___y_613_ = v___y_675_;
goto v___jp_608_;
}
else
{
lean_object* v___x_678_; lean_object* v_env_679_; lean_object* v_nextMacroScope_680_; lean_object* v_ngen_681_; lean_object* v_auxDeclNGen_682_; lean_object* v_traceState_683_; lean_object* v_messages_684_; lean_object* v_infoState_685_; lean_object* v_snapshotTasks_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v___x_678_ = lean_st_ref_take(v___y_675_);
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
v___x_690_ = l_Lean_Kernel_enableDiag(v_env_679_, v___y_671_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 5, v___x_595_);
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
lean_ctor_set(v_reuseFailAlloc_694_, 5, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_694_, 6, v_messages_684_);
lean_ctor_set(v_reuseFailAlloc_694_, 7, v_infoState_685_);
lean_ctor_set(v_reuseFailAlloc_694_, 8, v_snapshotTasks_686_);
v___x_692_ = v_reuseFailAlloc_694_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_st_ref_set(v___y_675_, v___x_692_);
v___y_609_ = v___y_671_;
v___y_610_ = v___y_674_;
v___y_611_ = v___y_673_;
v___y_612_ = v___y_672_;
v___y_613_ = v___y_675_;
goto v___jp_608_;
}
}
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
v___x_734_ = lean_obj_once(&l_Lean_PrettyPrinter_ppExprLegacy___closed__25, &l_Lean_PrettyPrinter_ppExprLegacy___closed__25_once, _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__25);
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
v___x_737_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_opts_577_, v___x_709_);
v___x_738_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_732_);
lean_dec_ref(v_env_732_);
if (v___x_738_ == 0)
{
if (v___x_737_ == 0)
{
v___y_671_ = v___x_737_;
v___y_672_ = v___x_736_;
v___y_673_ = v___x_733_;
v___y_674_ = v___x_714_;
v___y_675_ = v___y_713_;
v___y_676_ = v___x_586_;
goto v___jp_670_;
}
else
{
v___y_671_ = v___x_737_;
v___y_672_ = v___x_736_;
v___y_673_ = v___x_733_;
v___y_674_ = v___x_714_;
v___y_675_ = v___y_713_;
v___y_676_ = v___x_738_;
goto v___jp_670_;
}
}
else
{
v___y_671_ = v___x_737_;
v___y_672_ = v___x_736_;
v___y_673_ = v___x_733_;
v___y_674_ = v___x_714_;
v___y_675_ = v___y_713_;
v___y_676_ = v___x_737_;
goto v___jp_670_;
}
}
}
}
v___jp_743_:
{
uint8_t v___x_745_; 
v___x_745_ = lean_bool_not(v___y_744_);
if (v___x_745_ == 0)
{
lean_inc(v___x_607_);
v___y_712_ = v___x_706_;
v___y_713_ = v___x_607_;
goto v___jp_711_;
}
else
{
lean_object* v___x_746_; lean_object* v_env_747_; lean_object* v_nextMacroScope_748_; lean_object* v_ngen_749_; lean_object* v_auxDeclNGen_750_; lean_object* v_traceState_751_; lean_object* v_messages_752_; lean_object* v_infoState_753_; lean_object* v_snapshotTasks_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_763_; 
v___x_746_ = lean_st_ref_take(v___x_607_);
v_env_747_ = lean_ctor_get(v___x_746_, 0);
v_nextMacroScope_748_ = lean_ctor_get(v___x_746_, 1);
v_ngen_749_ = lean_ctor_get(v___x_746_, 2);
v_auxDeclNGen_750_ = lean_ctor_get(v___x_746_, 3);
v_traceState_751_ = lean_ctor_get(v___x_746_, 4);
v_messages_752_ = lean_ctor_get(v___x_746_, 6);
v_infoState_753_ = lean_ctor_get(v___x_746_, 7);
v_snapshotTasks_754_ = lean_ctor_get(v___x_746_, 8);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_746_, 5);
lean_dec(v_unused_764_);
v___x_756_ = v___x_746_;
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_snapshotTasks_754_);
lean_inc(v_infoState_753_);
lean_inc(v_messages_752_);
lean_inc(v_traceState_751_);
lean_inc(v_auxDeclNGen_750_);
lean_inc(v_ngen_749_);
lean_inc(v_nextMacroScope_748_);
lean_inc(v_env_747_);
lean_dec(v___x_746_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_763_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = l_Lean_Kernel_enableDiag(v_env_747_, v___x_710_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 5, v___x_595_);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_nextMacroScope_748_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_ngen_749_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_auxDeclNGen_750_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_traceState_751_);
lean_ctor_set(v_reuseFailAlloc_762_, 5, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_762_, 6, v_messages_752_);
lean_ctor_set(v_reuseFailAlloc_762_, 7, v_infoState_753_);
lean_ctor_set(v_reuseFailAlloc_762_, 8, v_snapshotTasks_754_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = lean_st_ref_set(v___x_607_, v___x_760_);
lean_inc(v___x_607_);
v___y_712_ = v___x_706_;
v___y_713_ = v___x_607_;
goto v___jp_711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprLegacy___boxed(lean_object* v_env_766_, lean_object* v_mctx_767_, lean_object* v_lctx_768_, lean_object* v_opts_769_, lean_object* v_e_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_PrettyPrinter_ppExprLegacy(v_env_766_, v_mctx_767_, v_lctx_768_, v_opts_769_, v_e_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppLevel(lean_object* v_l_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = l_Lean_PrettyPrinter_delabLevel(v_l_776_, v___x_782_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_785_ = ((lean_object*)(l_Lean_PrettyPrinter_ppLevel___closed__1));
v___x_786_ = l_Lean_PrettyPrinter_ppCategory(v___x_785_, v_a_784_, v_a_779_, v_a_780_);
return v___x_786_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_a_787_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_783_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_783_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppLevel___boxed(lean_object* v_l_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_PrettyPrinter_ppLevel(v_l_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic(lean_object* v_stx_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l_Lean_PrettyPrinter_ppTactic___closed__1));
v___x_810_ = l_Lean_PrettyPrinter_ppCategory(v___x_809_, v_stx_805_, v_a_806_, v_a_807_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic___boxed(lean_object* v_stx_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_PrettyPrinter_ppTactic(v_stx_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object* v_stx_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l_Lean_PrettyPrinter_ppCommand___closed__1));
v___x_824_ = l_Lean_PrettyPrinter_ppCategory(v___x_823_, v_stx_819_, v_a_820_, v_a_821_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand___boxed(lean_object* v_stx_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_PrettyPrinter_ppCommand(v_stx_825_, v_a_826_, v_a_827_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule(lean_object* v_stx_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_PrettyPrinter_ppModule___closed__0));
v___x_837_ = l_Lean_PrettyPrinter_parenthesize(v___x_836_, v_stx_832_, v_a_833_, v_a_834_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = ((lean_object*)(l_Lean_PrettyPrinter_ppModule___closed__1));
v___x_840_ = l_Lean_PrettyPrinter_format(v___x_839_, v_a_838_, v_a_833_, v_a_834_);
return v___x_840_;
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
v_a_841_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_837_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_837_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule___boxed(lean_object* v_stx_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_PrettyPrinter_ppModule(v_stx_849_, v_a_850_, v_a_851_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
return v_res_853_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_854_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
lean_ctor_set(v___x_859_, 2, v___x_858_);
lean_ctor_set(v___x_859_, 3, v___x_858_);
lean_ctor_set(v___x_859_, 4, v___x_857_);
lean_ctor_set(v___x_859_, 5, v___x_857_);
lean_ctor_set(v___x_859_, 6, v___x_857_);
lean_ctor_set(v___x_859_, 7, v___x_857_);
lean_ctor_set(v___x_859_, 8, v___x_857_);
lean_ctor_set(v___x_859_, 9, v___x_857_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = lean_unsigned_to_nat(32u);
v___x_861_ = lean_mk_empty_array_with_capacity(v___x_860_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_863_ = ((size_t)5ULL);
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = lean_unsigned_to_nat(32u);
v___x_866_ = lean_mk_empty_array_with_capacity(v___x_865_);
v___x_867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_868_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v___x_866_);
lean_ctor_set(v___x_868_, 2, v___x_864_);
lean_ctor_set(v___x_868_, 3, v___x_864_);
lean_ctor_set_usize(v___x_868_, 4, v___x_863_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_869_ = lean_box(1);
v___x_870_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_870_);
lean_ctor_set(v___x_872_, 2, v___x_869_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_875_ = l_Lean_stringToMessageData(v___x_874_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_893_ = l_Lean_stringToMessageData(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_894_, lean_object* v_declHint_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_env_899_; uint8_t v___y_901_; uint8_t v___x_957_; uint8_t v___x_958_; 
v___x_898_ = lean_st_ref_get(v___y_896_);
v_env_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc_ref(v_env_899_);
lean_dec(v___x_898_);
v___x_957_ = l_Lean_Name_isAnonymous(v_declHint_895_);
v___x_958_ = lean_bool_not(v___x_957_);
if (v___x_958_ == 0)
{
v___y_901_ = v___x_958_;
goto v___jp_900_;
}
else
{
uint8_t v_isExporting_959_; 
v_isExporting_959_ = lean_ctor_get_uint8(v_env_899_, sizeof(void*)*8);
v___y_901_ = v_isExporting_959_;
goto v___jp_900_;
}
v___jp_900_:
{
if (v___y_901_ == 0)
{
lean_object* v___x_902_; 
lean_dec_ref(v_env_899_);
lean_dec(v_declHint_895_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v_msg_894_);
return v___x_902_;
}
else
{
uint8_t v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_903_ = 0;
lean_inc_ref(v_env_899_);
v___x_904_ = l_Lean_Environment_setExporting(v_env_899_, v___x_903_);
lean_inc(v_declHint_895_);
lean_inc_ref(v___x_904_);
v___x_905_ = l_Lean_Environment_contains(v___x_904_, v_declHint_895_, v___y_901_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
lean_dec_ref(v___x_904_);
lean_dec_ref(v_env_899_);
lean_dec(v_declHint_895_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v_msg_894_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_c_912_; lean_object* v___x_913_; 
v___x_907_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_909_ = l_Lean_Options_empty;
v___x_910_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_910_, 0, v___x_904_);
lean_ctor_set(v___x_910_, 1, v___x_907_);
lean_ctor_set(v___x_910_, 2, v___x_908_);
lean_ctor_set(v___x_910_, 3, v___x_909_);
lean_inc(v_declHint_895_);
v___x_911_ = l_Lean_MessageData_ofConstName(v_declHint_895_, v___x_903_);
v_c_912_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_912_, 0, v___x_910_);
lean_ctor_set(v_c_912_, 1, v___x_911_);
v___x_913_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_899_, v_declHint_895_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec_ref(v_env_899_);
lean_dec(v_declHint_895_);
v___x_914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v_c_912_);
v___x_916_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l_Lean_MessageData_note(v___x_917_);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v_msg_894_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
else
{
lean_object* v_val_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_956_; 
v_val_921_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_956_ == 0)
{
v___x_923_ = v___x_913_;
v_isShared_924_ = v_isSharedCheck_956_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_val_921_);
lean_dec(v___x_913_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_956_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_mod_928_; uint8_t v___x_929_; 
v___x_925_ = lean_box(0);
v___x_926_ = l_Lean_Environment_header(v_env_899_);
lean_dec_ref(v_env_899_);
v___x_927_ = l_Lean_EnvironmentHeader_moduleNames(v___x_926_);
v_mod_928_ = lean_array_get(v___x_925_, v___x_927_, v_val_921_);
lean_dec(v_val_921_);
lean_dec_ref(v___x_927_);
v___x_929_ = l_Lean_isPrivateName(v_declHint_895_);
lean_dec(v_declHint_895_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v_c_912_);
v___x_932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_MessageData_ofName(v_mod_928_);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_MessageData_note(v___x_937_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v_msg_894_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
if (v_isShared_924_ == 0)
{
lean_ctor_set_tag(v___x_923_, 0);
lean_ctor_set(v___x_923_, 0, v___x_939_);
v___x_941_ = v___x_923_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_943_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_c_912_);
v___x_945_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_MessageData_ofName(v_mod_928_);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Lean_MessageData_note(v___x_950_);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v_msg_894_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
if (v_isShared_924_ == 0)
{
lean_ctor_set_tag(v___x_923_, 0);
lean_ctor_set(v___x_923_, 0, v___x_952_);
v___x_954_ = v___x_923_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_960_, lean_object* v_declHint_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_960_, v_declHint_961_, v___y_962_);
lean_dec(v___y_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_965_, lean_object* v_declHint_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_982_; 
v___x_972_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_965_, v_declHint_966_, v___y_970_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_982_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_982_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_982_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_977_ = l_Lean_unknownIdentifierMessageTag;
v___x_978_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_a_973_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_978_);
v___x_980_ = v___x_975_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_983_, lean_object* v_declHint_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_983_, v_declHint_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(lean_object* v_msgData_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; lean_object* v_env_998_; lean_object* v___x_999_; lean_object* v_mctx_1000_; lean_object* v_lctx_1001_; lean_object* v_options_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_997_ = lean_st_ref_get(v___y_995_);
v_env_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc_ref(v_env_998_);
lean_dec(v___x_997_);
v___x_999_ = lean_st_ref_get(v___y_993_);
v_mctx_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc_ref(v_mctx_1000_);
lean_dec(v___x_999_);
v_lctx_1001_ = lean_ctor_get(v___y_992_, 2);
v_options_1002_ = lean_ctor_get(v___y_994_, 2);
lean_inc_ref(v_options_1002_);
lean_inc_ref(v_lctx_1001_);
v___x_1003_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1003_, 0, v_env_998_);
lean_ctor_set(v___x_1003_, 1, v_mctx_1000_);
lean_ctor_set(v___x_1003_, 2, v_lctx_1001_);
lean_ctor_set(v___x_1003_, 3, v_options_1002_);
v___x_1004_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v_msgData_991_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* v_msgData_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_ref_1019_; lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1029_; 
v_ref_1019_ = lean_ctor_get(v___y_1016_, 5);
v___x_1020_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
lean_inc(v_ref_1019_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v_ref_1019_);
lean_ctor_set(v___x_1025_, 1, v_a_1021_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
lean_ctor_set(v___x_1023_, 0, v___x_1025_);
v___x_1027_ = v___x_1023_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_1037_, lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_fileName_1044_; lean_object* v_fileMap_1045_; lean_object* v_options_1046_; lean_object* v_currRecDepth_1047_; lean_object* v_maxRecDepth_1048_; lean_object* v_ref_1049_; lean_object* v_currNamespace_1050_; lean_object* v_openDecls_1051_; lean_object* v_initHeartbeats_1052_; lean_object* v_maxHeartbeats_1053_; lean_object* v_quotContext_1054_; lean_object* v_currMacroScope_1055_; uint8_t v_diag_1056_; lean_object* v_cancelTk_x3f_1057_; uint8_t v_suppressElabErrors_1058_; lean_object* v_inheritedTraceOptions_1059_; lean_object* v_ref_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_fileName_1044_ = lean_ctor_get(v___y_1041_, 0);
v_fileMap_1045_ = lean_ctor_get(v___y_1041_, 1);
v_options_1046_ = lean_ctor_get(v___y_1041_, 2);
v_currRecDepth_1047_ = lean_ctor_get(v___y_1041_, 3);
v_maxRecDepth_1048_ = lean_ctor_get(v___y_1041_, 4);
v_ref_1049_ = lean_ctor_get(v___y_1041_, 5);
v_currNamespace_1050_ = lean_ctor_get(v___y_1041_, 6);
v_openDecls_1051_ = lean_ctor_get(v___y_1041_, 7);
v_initHeartbeats_1052_ = lean_ctor_get(v___y_1041_, 8);
v_maxHeartbeats_1053_ = lean_ctor_get(v___y_1041_, 9);
v_quotContext_1054_ = lean_ctor_get(v___y_1041_, 10);
v_currMacroScope_1055_ = lean_ctor_get(v___y_1041_, 11);
v_diag_1056_ = lean_ctor_get_uint8(v___y_1041_, sizeof(void*)*14);
v_cancelTk_x3f_1057_ = lean_ctor_get(v___y_1041_, 12);
v_suppressElabErrors_1058_ = lean_ctor_get_uint8(v___y_1041_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1059_ = lean_ctor_get(v___y_1041_, 13);
v_ref_1060_ = l_Lean_replaceRef(v_ref_1037_, v_ref_1049_);
lean_inc_ref(v_inheritedTraceOptions_1059_);
lean_inc(v_cancelTk_x3f_1057_);
lean_inc(v_currMacroScope_1055_);
lean_inc(v_quotContext_1054_);
lean_inc(v_maxHeartbeats_1053_);
lean_inc(v_initHeartbeats_1052_);
lean_inc(v_openDecls_1051_);
lean_inc(v_currNamespace_1050_);
lean_inc(v_maxRecDepth_1048_);
lean_inc(v_currRecDepth_1047_);
lean_inc_ref(v_options_1046_);
lean_inc_ref(v_fileMap_1045_);
lean_inc_ref(v_fileName_1044_);
v___x_1061_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1061_, 0, v_fileName_1044_);
lean_ctor_set(v___x_1061_, 1, v_fileMap_1045_);
lean_ctor_set(v___x_1061_, 2, v_options_1046_);
lean_ctor_set(v___x_1061_, 3, v_currRecDepth_1047_);
lean_ctor_set(v___x_1061_, 4, v_maxRecDepth_1048_);
lean_ctor_set(v___x_1061_, 5, v_ref_1060_);
lean_ctor_set(v___x_1061_, 6, v_currNamespace_1050_);
lean_ctor_set(v___x_1061_, 7, v_openDecls_1051_);
lean_ctor_set(v___x_1061_, 8, v_initHeartbeats_1052_);
lean_ctor_set(v___x_1061_, 9, v_maxHeartbeats_1053_);
lean_ctor_set(v___x_1061_, 10, v_quotContext_1054_);
lean_ctor_set(v___x_1061_, 11, v_currMacroScope_1055_);
lean_ctor_set(v___x_1061_, 12, v_cancelTk_x3f_1057_);
lean_ctor_set(v___x_1061_, 13, v_inheritedTraceOptions_1059_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*14, v_diag_1056_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*14 + 1, v_suppressElabErrors_1058_);
v___x_1062_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1038_, v___y_1039_, v___y_1040_, v___x_1061_, v___y_1042_);
lean_dec_ref_known(v___x_1061_, 14);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1063_, v_msg_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v_ref_1063_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1071_, lean_object* v_msg_1072_, lean_object* v_declHint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v_a_1080_; lean_object* v___x_1081_; 
v___x_1079_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1072_, v_declHint_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1071_, v_a_1080_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1082_, lean_object* v_msg_1083_, lean_object* v_declHint_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1082_, v_msg_1083_, v_declHint_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v_ref_1082_);
return v_res_1090_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1097_, lean_object* v_constName_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1104_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1105_ = 0;
lean_inc(v_constName_1098_);
v___x_1106_ = l_Lean_MessageData_ofConstName(v_constName_1098_, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1104_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1097_, v___x_1109_, v_constName_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1111_, lean_object* v_constName_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_1111_, v_constName_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v_ref_1111_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(lean_object* v_constName_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_ref_1125_; lean_object* v___x_1126_; 
v_ref_1125_ = lean_ctor_get(v___y_1122_, 5);
v___x_1126_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_1125_, v_constName_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(lean_object* v_constName_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v_env_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; 
v___x_1140_ = lean_st_ref_get(v___y_1138_);
v_env_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc_ref(v_env_1141_);
lean_dec(v___x_1140_);
v___x_1142_ = 0;
lean_inc(v_constName_1134_);
v___x_1143_ = l_Lean_Environment_find_x3f(v_env_1141_, v_constName_1134_, v___x_1142_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1144_;
}
else
{
lean_object* v_val_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_constName_1134_);
v_val_1145_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_val_1145_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 0);
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_val_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0___boxed(lean_object* v_constName_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(v_constName_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object* v_c_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1170_; 
lean_inc(v_c_1164_);
v___x_1170_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(v_c_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1232_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1232_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1232_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_options_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_options_1175_ = lean_ctor_get(v_a_1167_, 2);
v___x_1176_ = l_Lean_ConstantInfo_levelParams(v_a_1171_);
v___x_1177_ = lean_box(0);
v___x_1178_ = l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(v___x_1176_, v___x_1177_);
v___x_1179_ = l_Lean_Expr_const___override(v_c_1164_, v___x_1178_);
v___x_1180_ = l_Lean_pp_raw;
v___x_1181_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_options_1175_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_del_object(v___x_1173_);
lean_dec(v_a_1171_);
v___x_1182_ = lean_box(1);
v___x_1183_ = ((lean_object*)(l_Lean_PrettyPrinter_ppSignature___closed__0));
v___x_1184_ = l_Lean_PrettyPrinter_delabCore___redArg(v___x_1179_, v___x_1182_, v___x_1183_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v_fst_1186_; lean_object* v_snd_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1211_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v_fst_1186_ = lean_ctor_get(v_a_1185_, 0);
v_snd_1187_ = lean_ctor_get(v_a_1185_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_a_1185_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1189_ = v_a_1185_;
v_isShared_1190_ = v_isSharedCheck_1211_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_snd_1187_);
lean_inc(v_fst_1186_);
lean_dec(v_a_1185_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1211_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_PrettyPrinter_ppTerm(v_fst_1186_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1202_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1202_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v_a_1192_);
v___x_1197_ = v___x_1189_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1192_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_snd_1187_);
v___x_1197_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1199_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1197_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_del_object(v___x_1189_);
lean_dec(v_snd_1187_);
v_a_1203_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1191_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1191_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_a_1212_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1184_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1184_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1220_ = lean_expr_dbg_to_string(v___x_1179_);
lean_dec_ref(v___x_1179_);
v___x_1221_ = ((lean_object*)(l_Lean_PrettyPrinter_ppSignature___closed__1));
v___x_1222_ = lean_string_append(v___x_1220_, v___x_1221_);
v___x_1223_ = l_Lean_ConstantInfo_type(v_a_1171_);
lean_dec(v_a_1171_);
v___x_1224_ = lean_expr_dbg_to_string(v___x_1223_);
lean_dec_ref(v___x_1223_);
v___x_1225_ = lean_string_append(v___x_1222_, v___x_1224_);
lean_dec_ref(v___x_1224_);
v___x_1226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
v___x_1227_ = lean_box(1);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1226_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1228_);
v___x_1230_ = v___x_1173_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_c_1164_);
v_a_1233_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1170_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1170_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature___boxed(lean_object* v_c_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_PrettyPrinter_ppSignature(v_c_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(lean_object* v_00_u03b1_1248_, lean_object* v_constName_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_constName_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(v_00_u03b1_1256_, v_constName_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1264_, lean_object* v_ref_1265_, lean_object* v_constName_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_1265_, v_constName_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1273_, lean_object* v_ref_1274_, lean_object* v_constName_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(v_00_u03b1_1273_, v_ref_1274_, v_constName_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v_ref_1274_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1282_, lean_object* v_ref_1283_, lean_object* v_msg_1284_, lean_object* v_declHint_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1283_, v_msg_1284_, v_declHint_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_ref_1293_, lean_object* v_msg_1294_, lean_object* v_declHint_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1292_, v_ref_1293_, v_msg_1294_, v_declHint_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v_ref_1293_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1302_, lean_object* v_declHint_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1302_, v_declHint_1303_, v___y_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1310_, lean_object* v_declHint_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1310_, v_declHint_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1318_, lean_object* v_ref_1319_, lean_object* v_msg_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1319_, v_msg_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_ref_1328_, lean_object* v_msg_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1327_, v_ref_1328_, v_msg_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v_ref_1328_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1336_, lean_object* v_msg_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1344_, lean_object* v_msg_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1344_, v_msg_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(lean_object* v_x_1352_){
_start:
{
switch(lean_obj_tag(v_x_1352_))
{
case 3:
{
lean_object* v_a_1353_; 
v_a_1353_ = lean_ctor_get(v_x_1352_, 1);
lean_inc_ref(v_a_1353_);
lean_dec_ref_known(v_x_1352_, 2);
v_x_1352_ = v_a_1353_;
goto _start;
}
case 4:
{
lean_object* v_a_1355_; lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1364_; 
v_a_1355_ = lean_ctor_get(v_x_1352_, 0);
v_a_1356_ = lean_ctor_get(v_x_1352_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1358_ = v_x_1352_;
v_isShared_1359_ = v_isSharedCheck_1364_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_inc(v_a_1355_);
lean_dec(v_x_1352_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1364_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1356_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v___x_1360_);
v___x_1362_ = v___x_1358_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1355_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
case 5:
{
lean_object* v_a_1365_; lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1374_; 
v_a_1365_ = lean_ctor_get(v_x_1352_, 0);
v_a_1366_ = lean_ctor_get(v_x_1352_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1368_ = v_x_1352_;
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_inc(v_a_1365_);
lean_dec(v_x_1352_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1366_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 1, v___x_1370_);
v___x_1372_ = v___x_1368_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1365_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
case 6:
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1383_; 
v_a_1375_ = lean_ctor_get(v_x_1352_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1377_ = v_x_1352_;
v_isShared_1378_ = v_isSharedCheck_1383_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v_x_1352_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1383_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1379_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1375_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1379_);
v___x_1381_ = v___x_1377_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
case 7:
{
lean_object* v_a_1384_; lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1394_; 
v_a_1384_ = lean_ctor_get(v_x_1352_, 0);
v_a_1385_ = lean_ctor_get(v_x_1352_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1387_ = v_x_1352_;
v_isShared_1388_ = v_isSharedCheck_1394_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_inc(v_a_1384_);
lean_dec(v_x_1352_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1394_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1389_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1384_);
v___x_1390_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1385_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 1, v___x_1390_);
lean_ctor_set(v___x_1387_, 0, v___x_1389_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
case 8:
{
lean_object* v_a_1395_; lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1404_; 
v_a_1395_ = lean_ctor_get(v_x_1352_, 0);
v_a_1396_ = lean_ctor_get(v_x_1352_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1398_ = v_x_1352_;
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_inc(v_a_1395_);
lean_dec(v_x_1352_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1395_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
case 9:
{
lean_object* v_data_1405_; lean_object* v_msg_1406_; lean_object* v_children_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1418_; 
v_data_1405_ = lean_ctor_get(v_x_1352_, 0);
v_msg_1406_ = lean_ctor_get(v_x_1352_, 1);
v_children_1407_ = lean_ctor_get(v_x_1352_, 2);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1409_ = v_x_1352_;
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_children_1407_);
lean_inc(v_msg_1406_);
lean_inc(v_data_1405_);
lean_dec(v_x_1352_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; size_t v_sz_1412_; size_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1411_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1406_);
v_sz_1412_ = lean_array_size(v_children_1407_);
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(v_sz_1412_, v___x_1413_, v_children_1407_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 2, v___x_1414_);
lean_ctor_set(v___x_1409_, 1, v___x_1411_);
v___x_1416_ = v___x_1409_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_data_1405_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
default: 
{
return v_x_1352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(size_t v_sz_1419_, size_t v_i_1420_, lean_object* v_bs_1421_){
_start:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_usize_dec_lt(v_i_1420_, v_sz_1419_);
if (v___x_1422_ == 0)
{
return v_bs_1421_;
}
else
{
lean_object* v_v_1423_; lean_object* v___x_1424_; lean_object* v_bs_x27_1425_; lean_object* v___x_1426_; size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v_v_1423_ = lean_array_uget(v_bs_1421_, v_i_1420_);
v___x_1424_ = lean_unsigned_to_nat(0u);
v_bs_x27_1425_ = lean_array_uset(v_bs_1421_, v_i_1420_, v___x_1424_);
v___x_1426_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_v_1423_);
v___x_1427_ = ((size_t)1ULL);
v___x_1428_ = lean_usize_add(v_i_1420_, v___x_1427_);
v___x_1429_ = lean_array_uset(v_bs_x27_1425_, v_i_1420_, v___x_1426_);
v_i_1420_ = v___x_1428_;
v_bs_1421_ = v___x_1429_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0___boxed(lean_object* v_sz_1431_, lean_object* v_i_1432_, lean_object* v_bs_1433_){
_start:
{
size_t v_sz_boxed_1434_; size_t v_i_boxed_1435_; lean_object* v_res_1436_; 
v_sz_boxed_1434_ = lean_unbox_usize(v_sz_1431_);
lean_dec(v_sz_1431_);
v_i_boxed_1435_ = lean_unbox_usize(v_i_1432_);
lean_dec(v_i_1432_);
v_res_1436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(v_sz_boxed_1434_, v_i_boxed_1435_, v_bs_1433_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0(lean_object* v_throw_1437_, lean_object* v_x_1438_){
_start:
{
if (lean_obj_tag(v_x_1438_) == 0)
{
lean_object* v_ref_1439_; lean_object* v_msg_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1449_; 
v_ref_1439_ = lean_ctor_get(v_x_1438_, 0);
v_msg_1440_ = lean_ctor_get(v_x_1438_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_x_1438_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1442_ = v_x_1438_;
v_isShared_1443_ = v_isSharedCheck_1449_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_msg_1440_);
lean_inc(v_ref_1439_);
lean_dec(v_x_1438_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1449_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1440_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_ref_1439_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_apply_2(v_throw_1437_, lean_box(0), v___x_1446_);
return v___x_1447_;
}
}
}
else
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_apply_2(v_throw_1437_, lean_box(0), v_x_1438_);
return v___x_1450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(lean_object* v_inst_1451_, lean_object* v_x_1452_){
_start:
{
lean_object* v_throw_1453_; lean_object* v_tryCatch_1454_; lean_object* v___f_1455_; lean_object* v___x_1456_; 
v_throw_1453_ = lean_ctor_get(v_inst_1451_, 0);
lean_inc(v_throw_1453_);
v_tryCatch_1454_ = lean_ctor_get(v_inst_1451_, 1);
lean_inc(v_tryCatch_1454_);
lean_dec_ref(v_inst_1451_);
v___f_1455_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1455_, 0, v_throw_1453_);
v___x_1456_ = lean_apply_3(v_tryCatch_1454_, lean_box(0), v_x_1452_, v___f_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(lean_object* v_00_u03b1_1457_, lean_object* v_m_1458_, lean_object* v_inst_1459_, lean_object* v_x_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(v_inst_1459_, v_x_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; 
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1464_);
lean_inc_ref(v___y_1463_);
v___x_1468_ = lean_apply_5(v_x_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, lean_box(0));
if (lean_obj_tag(v___x_1468_) == 0)
{
return v___x_1468_;
}
else
{
lean_object* v_a_1469_; uint8_t v___y_1471_; uint8_t v___x_1490_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
v___x_1490_ = l_Lean_Exception_isInterrupt(v_a_1469_);
if (v___x_1490_ == 0)
{
uint8_t v___x_1491_; 
lean_inc(v_a_1469_);
v___x_1491_ = l_Lean_Exception_isRuntime(v_a_1469_);
v___y_1471_ = v___x_1491_;
goto v___jp_1470_;
}
else
{
v___y_1471_ = v___x_1490_;
goto v___jp_1470_;
}
v___jp_1470_:
{
if (v___y_1471_ == 0)
{
if (lean_obj_tag(v_a_1469_) == 0)
{
lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1488_; 
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v___x_1468_, 0);
lean_dec(v_unused_1489_);
v___x_1473_ = v___x_1468_;
v_isShared_1474_ = v_isSharedCheck_1488_;
goto v_resetjp_1472_;
}
else
{
lean_dec(v___x_1468_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1488_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_ref_1475_; lean_object* v_msg_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1487_; 
v_ref_1475_ = lean_ctor_get(v_a_1469_, 0);
v_msg_1476_ = lean_ctor_get(v_a_1469_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1478_ = v_a_1469_;
v_isShared_1479_ = v_isSharedCheck_1487_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_msg_1476_);
lean_inc(v_ref_1475_);
lean_dec(v_a_1469_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1487_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1476_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 1, v___x_1480_);
v___x_1482_ = v___x_1478_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_ref_1475_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1482_);
v___x_1484_ = v___x_1473_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
else
{
lean_dec(v_a_1469_);
return v___x_1468_;
}
}
else
{
lean_dec(v_a_1469_);
return v___x_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_x_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(v_x_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(v_x_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1507_, lean_object* v_x_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0(v_00_u03b1_1507_, v_x_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; 
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
v___x_1519_ = lean_apply_3(v_x_1515_, v___y_1516_, v___y_1517_, lean_box(0));
if (lean_obj_tag(v___x_1519_) == 0)
{
return v___x_1519_;
}
else
{
lean_object* v_a_1520_; uint8_t v___y_1522_; uint8_t v___x_1541_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
v___x_1541_ = l_Lean_Exception_isInterrupt(v_a_1520_);
if (v___x_1541_ == 0)
{
uint8_t v___x_1542_; 
lean_inc(v_a_1520_);
v___x_1542_ = l_Lean_Exception_isRuntime(v_a_1520_);
v___y_1522_ = v___x_1542_;
goto v___jp_1521_;
}
else
{
v___y_1522_ = v___x_1541_;
goto v___jp_1521_;
}
v___jp_1521_:
{
if (v___y_1522_ == 0)
{
if (lean_obj_tag(v_a_1520_) == 0)
{
lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1539_; 
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v___x_1519_, 0);
lean_dec(v_unused_1540_);
v___x_1524_ = v___x_1519_;
v_isShared_1525_ = v_isSharedCheck_1539_;
goto v_resetjp_1523_;
}
else
{
lean_dec(v___x_1519_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1539_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v_ref_1526_; lean_object* v_msg_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1538_; 
v_ref_1526_ = lean_ctor_get(v_a_1520_, 0);
v_msg_1527_ = lean_ctor_get(v_a_1520_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_a_1520_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1529_ = v_a_1520_;
v_isShared_1530_ = v_isSharedCheck_1538_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_msg_1527_);
lean_inc(v_ref_1526_);
lean_dec(v_a_1520_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1538_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1531_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_1527_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 1, v___x_1531_);
v___x_1533_ = v___x_1529_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_ref_1526_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1535_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1533_);
v___x_1535_ = v___x_1524_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
else
{
lean_dec(v_a_1520_);
return v___x_1519_;
}
}
else
{
lean_dec(v_a_1520_);
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(v_x_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b1_1548_, lean_object* v_x_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(v_x_1549_, v___y_1550_, v___y_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b1_1554_, lean_object* v_x_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1(v_00_u03b1_1554_, v_x_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object* v_ctx_1561_, lean_object* v_e_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1564_ = lean_box(1);
v___x_1565_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_));
v___x_1566_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___boxed), 8, 3);
lean_closure_set(v___x_1566_, 0, v_e_1562_);
lean_closure_set(v___x_1566_, 1, v___x_1564_);
lean_closure_set(v___x_1566_, 2, v___x_1565_);
v___x_1567_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1567_, 0, lean_box(0));
lean_closure_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1561_, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_ctx_1569_, lean_object* v_e_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_1569_, v_e_1570_);
lean_dec_ref(v_ctx_1569_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object* v_ctx_1573_, lean_object* v_n_1574_){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___boxed), 6, 1);
lean_closure_set(v___x_1576_, 0, v_n_1574_);
v___x_1577_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1577_, 0, lean_box(0));
lean_closure_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1573_, v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_ctx_1579_, lean_object* v_n_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_1579_, v_n_1580_);
lean_dec_ref(v_ctx_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object* v_ctx_1583_, lean_object* v_l_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppLevel___boxed), 6, 1);
lean_closure_set(v___x_1586_, 0, v_l_1584_);
v___x_1587_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1587_, 0, lean_box(0));
lean_closure_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1583_, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_ctx_1589_, lean_object* v_l_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_1589_, v_l_1590_);
lean_dec_ref(v_ctx_1589_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object* v_ctx_1593_, lean_object* v_mvarId_1594_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal___boxed), 6, 1);
lean_closure_set(v___x_1596_, 0, v_mvarId_1594_);
v___x_1597_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed), 7, 2);
lean_closure_set(v___x_1597_, 0, lean_box(0));
lean_closure_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1593_, v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_ctx_1599_, lean_object* v_mvarId_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_1599_, v_mvarId_1600_);
lean_dec_ref(v_ctx_1599_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(lean_object* v_ctx_1603_, lean_object* v_stx_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTerm___boxed), 4, 1);
lean_closure_set(v___x_1606_, 0, v_stx_1604_);
v___x_1607_ = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___boxed), 5, 2);
lean_closure_set(v___x_1607_, 0, lean_box(0));
lean_closure_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = l_Lean_PPContext_runCoreM___redArg(v_ctx_1603_, v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_ctx_1609_, lean_object* v_stx_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_1609_, v_stx_1610_);
lean_dec_ref(v_ctx_1609_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1625_ = l_Lean_ppFnsRef;
v___x_1626_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_));
v___x_1627_ = lean_st_ref_set(v___x_1625_, v___x_1626_);
v___x_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_();
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1681_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_));
v___x_1682_ = 0;
v___x_1683_ = ((lean_object*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_));
v___x_1684_ = l_Lean_registerTraceClass(v___x_1681_, v___x_1682_, v___x_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2____boxed(lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_();
return v_res_1686_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1690_ = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
v___x_1691_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
v___x_1692_ = ((lean_object*)(l_Lean_PrettyPrinter_registerParserCompilers___closed__1));
v___x_1693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v___x_1691_);
lean_ctor_set(v___x_1693_, 2, v___x_1690_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1697_ = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
v___x_1698_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_1699_ = ((lean_object*)(l_Lean_PrettyPrinter_registerParserCompilers___closed__4));
v___x_1700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1699_);
lean_ctor_set(v___x_1700_, 1, v___x_1698_);
lean_ctor_set(v___x_1700_, 2, v___x_1697_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers(){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = lean_obj_once(&l_Lean_PrettyPrinter_registerParserCompilers___closed__2, &l_Lean_PrettyPrinter_registerParserCompilers___closed__2_once, _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2);
v___x_1703_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v___x_1702_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_dec_ref_known(v___x_1703_, 1);
v___x_1704_ = lean_obj_once(&l_Lean_PrettyPrinter_registerParserCompilers___closed__5, &l_Lean_PrettyPrinter_registerParserCompilers___closed__5_once, _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5);
v___x_1705_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v___x_1704_);
return v___x_1705_;
}
else
{
return v___x_1703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers___boxed(lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_PrettyPrinter_registerParserCompilers();
return v_res_1707_;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2));
v___x_1713_ = l_Lean_stringToMessageData(v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0(lean_object* v_fmt_1714_, lean_object* v_ctx_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1715_, v_fmt_1714_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1739_; 
v_a_1726_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1728_ = v___x_1717_;
v_isShared_1729_ = v_isSharedCheck_1739_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1717_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1739_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1730_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1, &l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1);
v___x_1731_ = lean_io_error_to_string(v_a_1726_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set_tag(v___x_1728_, 3);
lean_ctor_set(v___x_1728_, 0, v___x_1731_);
v___x_1733_ = v___x_1728_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1734_ = l_Lean_MessageData_ofFormat(v___x_1733_);
v___x_1735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1730_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3, &l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3);
v___x_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1735_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
return v___x_1737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed(lean_object* v_fmt_1740_, lean_object* v_ctx_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_MessageData_ofFormatWithInfosM___lam__0(v_fmt_1740_, v_ctx_1741_);
lean_dec_ref(v_ctx_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofFormatWithInfosM___lam__1(lean_object* v_x_1744_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = 0;
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed(lean_object* v_x_1746_){
_start:
{
uint8_t v_res_1747_; lean_object* v_r_1748_; 
v_res_1747_ = l_Lean_MessageData_ofFormatWithInfosM___lam__1(v_x_1746_);
lean_dec_ref(v_x_1746_);
v_r_1748_ = lean_box(v_res_1747_);
return v_r_1748_;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1));
v___x_1753_ = l_Lean_MessageData_ofFormat(v___x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2(lean_object* v_x_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2, &l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed(lean_object* v_x_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_MessageData_ofFormatWithInfosM___lam__2(v_x_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM(lean_object* v_fmt_1762_){
_start:
{
lean_object* v___f_1763_; lean_object* v___f_1764_; lean_object* v___f_1765_; lean_object* v___x_1766_; 
v___f_1763_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1763_, 0, v_fmt_1762_);
v___f_1764_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__0));
v___f_1765_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__1));
v___x_1766_ = l_Lean_MessageData_lazy(v___f_1763_, v___f_1764_, v___f_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_ofConst_spec__0(lean_object* v___x_1767_, lean_object* v_msg_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_panic_fn_borrowed(v___x_1767_, v_msg_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_ofConst_spec__0___boxed(lean_object* v___x_1770_, lean_object* v_msg_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_panic___at___00Lean_MessageData_ofConst_spec__0(v___x_1770_, v_msg_1771_);
lean_dec_ref(v___x_1770_);
return v_res_1772_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__1(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__0));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__2(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_box(1);
v___x_1777_ = l_Lean_MessageData_ofFormat(v___x_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__3(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__2, &l_Lean_MessageData_ofConst___closed__2_once, _init_l_Lean_MessageData_ofConst___closed__2);
v___x_1779_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__1, &l_Lean_MessageData_ofConst___closed__1_once, _init_l_Lean_MessageData_ofConst___closed__1);
v___x_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
lean_ctor_set(v___x_1780_, 1, v___x_1778_);
return v___x_1780_;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__7(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1784_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__6));
v___x_1785_ = lean_unsigned_to_nat(4u);
v___x_1786_ = lean_unsigned_to_nat(156u);
v___x_1787_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__5));
v___x_1788_ = ((lean_object*)(l_Lean_MessageData_ofConst___closed__4));
v___x_1789_ = l_mkPanicMessageWithDecl(v___x_1788_, v___x_1787_, v___x_1786_, v___x_1785_, v___x_1784_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConst(lean_object* v_e_1790_){
_start:
{
uint8_t v___x_1791_; 
v___x_1791_ = l_Lean_Expr_isConst(v_e_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1792_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__3, &l_Lean_MessageData_ofConst___closed__3_once, _init_l_Lean_MessageData_ofConst___closed__3);
v___x_1793_ = l_Lean_MessageData_ofExpr(v_e_1790_);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__7, &l_Lean_MessageData_ofConst___closed__7_once, _init_l_Lean_MessageData_ofConst___closed__7);
v___x_1796_ = lean_panic_fn_borrowed(v___x_1794_, v___x_1795_);
lean_dec_ref_known(v___x_1794_, 2);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_delab_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1797_ = ((lean_object*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1));
v___x_1798_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1798_, 0, v___x_1791_);
v___x_1799_ = ((lean_object*)(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3));
v_delab_1800_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed), 11, 4);
lean_closure_set(v_delab_1800_, 0, lean_box(0));
lean_closure_set(v_delab_1800_, 1, v___x_1797_);
lean_closure_set(v_delab_1800_, 2, v___x_1798_);
lean_closure_set(v_delab_1800_, 3, v___x_1799_);
v___x_1801_ = lean_box(1);
v___x_1802_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___boxed), 8, 3);
lean_closure_set(v___x_1802_, 0, v_e_1790_);
lean_closure_set(v___x_1802_, 1, v___x_1801_);
lean_closure_set(v___x_1802_, 2, v_delab_1800_);
v___x_1803_ = l_Lean_MessageData_ofFormatWithInfosM(v___x_1802_);
return v___x_1803_;
}
}
}
static lean_object* _init_l_Lean_MessageData_signature___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = ((lean_object*)(l_Lean_MessageData_signature___lam__0___closed__0));
v___x_1806_ = l_Lean_stringToMessageData(v___x_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0(lean_object* v_c_1807_, lean_object* v_ctx_1808_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_inc(v_c_1807_);
v___x_1810_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppSignature___boxed), 6, 1);
lean_closure_set(v___x_1810_, 0, v_c_1807_);
v___x_1811_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_1808_, v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v_c_1807_);
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1837_; 
v_a_1820_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1822_ = v___x_1811_;
v_isShared_1823_ = v_isSharedCheck_1837_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1811_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1837_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1824_ = lean_obj_once(&l_Lean_MessageData_signature___lam__0___closed__1, &l_Lean_MessageData_signature___lam__0___closed__1_once, _init_l_Lean_MessageData_signature___lam__0___closed__1);
v___x_1825_ = lean_io_error_to_string(v_a_1820_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 3);
lean_ctor_set(v___x_1822_, 0, v___x_1825_);
v___x_1827_ = v___x_1822_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1828_ = l_Lean_MessageData_ofFormat(v___x_1827_);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1824_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_obj_once(&l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3, &l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once, _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_obj_once(&l_Lean_MessageData_ofConst___closed__2, &l_Lean_MessageData_ofConst___closed__2_once, _init_l_Lean_MessageData_ofConst___closed__2);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = l_Lean_MessageData_ofName(v_c_1807_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
return v___x_1835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0___boxed(lean_object* v_c_1838_, lean_object* v_ctx_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_MessageData_signature___lam__0(v_c_1838_, v_ctx_1839_);
lean_dec_ref(v_ctx_1839_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature(lean_object* v_c_1842_){
_start:
{
lean_object* v___f_1843_; lean_object* v___f_1844_; lean_object* v___f_1845_; lean_object* v___x_1846_; 
v___f_1843_ = lean_alloc_closure((void*)(l_Lean_MessageData_signature___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1843_, 0, v_c_1842_);
v___f_1844_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__0));
v___f_1845_ = ((lean_object*)(l_Lean_MessageData_ofFormatWithInfosM___closed__1));
v___x_1846_ = l_Lean_MessageData_lazy(v___f_1843_, v___f_1844_, v___f_1845_);
return v___x_1846_;
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
