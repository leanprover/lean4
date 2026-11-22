// Lean compiler output
// Module: Lean.Elab.DeprecatedSyntax.Basic
// Imports: public import Lean.MonadEnv public import Lean.Linter.Init public import Lean.Elab.Util import Lean.Meta.Hint import Lean.Elab.DeprecatedSyntax.FormatReplacement
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Core_shouldCheckDeprecated___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Parser_getSyntaxNodeKindCategories(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_eraseQuoteMacroScopes(lean_object*);
lean_object* l_Lean_Elab_DeprecatedSyntax_formatReplacement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 149, 21, 131, 183, 70, 101, 25)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "if true, generate warnings when deprecated syntax is used"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(248, 165, 85, 201, 27, 48, 185, 203)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(73, 92, 249, 154, 145, 175, 141, 131)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_deprecated_syntax;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deprecatedSyntaxExt"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 151, 2, 103, 84, 175, 195, 226)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_deprecatedSyntaxExt;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "deprecatedSyntaxReplacementExt"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 133, 149, 127, 150, 83, 233, 160)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_deprecatedSyntaxReplacementExt;
LEAN_EXPORT uint8_t l_Lean_Elab_isDeprecatedSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isDeprecatedSyntax___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__0 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__1 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Replace the deprecated syntax:"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__0 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__1 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__0 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "syntax '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__0 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__1;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "' has been deprecated"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__2 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___closed__2_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__3;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "macro '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__4 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___closed__4_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__5;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "' produces deprecated syntax '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__6 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___closed__6_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__7;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__8 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___closed__8_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__9;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " produces deprecated syntax '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__10 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___closed__10_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__11;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " (expanded from '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__12 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___closed__12_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__13;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "')"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__14 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___closed__14_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "quotation uses deprecated syntax '"};
static const lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__0 = (const lean_object*)&l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_(lean_object* v_m_62_, lean_object* v_e_63_){
_start:
{
lean_object* v_kind_64_; lean_object* v___x_65_; 
v_kind_64_ = lean_ctor_get(v_e_63_, 0);
lean_inc(v_kind_64_);
v___x_65_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_kind_64_, v_e_63_, v_m_62_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_(lean_object* v_es_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_array_mk(v_es_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_68_, size_t v_i_69_, size_t v_stop_70_, lean_object* v_b_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = lean_usize_dec_eq(v_i_69_, v_stop_70_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v_kind_74_; lean_object* v___x_75_; size_t v___x_76_; size_t v___x_77_; 
v___x_73_ = lean_array_uget_borrowed(v_as_68_, v_i_69_);
v_kind_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v___x_73_);
lean_inc(v_kind_74_);
v___x_75_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_kind_74_, v___x_73_, v_b_71_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_add(v_i_69_, v___x_76_);
v_i_69_ = v___x_77_;
v_b_71_ = v___x_75_;
goto _start;
}
else
{
return v_b_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_79_, lean_object* v_i_80_, lean_object* v_stop_81_, lean_object* v_b_82_){
_start:
{
size_t v_i_boxed_83_; size_t v_stop_boxed_84_; lean_object* v_res_85_; 
v_i_boxed_83_ = lean_unbox_usize(v_i_80_);
lean_dec(v_i_80_);
v_stop_boxed_84_ = lean_unbox_usize(v_stop_81_);
lean_dec(v_stop_81_);
v_res_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__0(v_as_79_, v_i_boxed_83_, v_stop_boxed_84_, v_b_82_);
lean_dec_ref(v_as_79_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_86_, size_t v_i_87_, size_t v_stop_88_, lean_object* v_b_89_){
_start:
{
lean_object* v___y_91_; uint8_t v___x_95_; 
v___x_95_ = lean_usize_dec_eq(v_i_87_, v_stop_88_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_96_ = lean_array_uget_borrowed(v_as_86_, v_i_87_);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_array_get_size(v___x_96_);
v___x_99_ = lean_nat_dec_lt(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
v___y_91_ = v_b_89_;
goto v___jp_90_;
}
else
{
size_t v___x_100_; size_t v___x_101_; lean_object* v___x_102_; 
v___x_100_ = ((size_t)0ULL);
v___x_101_ = lean_usize_of_nat(v___x_98_);
v___x_102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__0(v___x_96_, v___x_100_, v___x_101_, v_b_89_);
v___y_91_ = v___x_102_;
goto v___jp_90_;
}
}
else
{
return v_b_89_;
}
v___jp_90_:
{
size_t v___x_92_; size_t v___x_93_; 
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_add(v_i_87_, v___x_92_);
v_i_87_ = v___x_93_;
v_b_89_ = v___y_91_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_103_, lean_object* v_i_104_, lean_object* v_stop_105_, lean_object* v_b_106_){
_start:
{
size_t v_i_boxed_107_; size_t v_stop_boxed_108_; lean_object* v_res_109_; 
v_i_boxed_107_ = lean_unbox_usize(v_i_104_);
lean_dec(v_i_104_);
v_stop_boxed_108_ = lean_unbox_usize(v_stop_105_);
lean_dec(v_stop_105_);
v_res_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_103_, v_i_boxed_107_, v_stop_boxed_108_, v_b_106_);
lean_dec_ref(v_as_103_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0(lean_object* v_initState_110_, lean_object* v_as_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_array_get_size(v_as_111_);
v___x_114_ = lean_nat_dec_lt(v___x_112_, v___x_113_);
if (v___x_114_ == 0)
{
return v_initState_110_;
}
else
{
size_t v___x_115_; size_t v___x_116_; lean_object* v___x_117_; 
v___x_115_ = ((size_t)0ULL);
v___x_116_ = lean_usize_of_nat(v___x_113_);
v___x_117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_111_, v___x_115_, v___x_116_, v_initState_110_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_118_, lean_object* v_as_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2__spec__0(v_initState_118_, v_as_119_);
lean_dec_ref(v_as_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_));
v___x_141_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2____boxed(lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_();
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___redArg(lean_object* v_k_144_, lean_object* v_t_145_){
_start:
{
if (lean_obj_tag(v_t_145_) == 0)
{
lean_object* v_k_146_; lean_object* v_v_147_; lean_object* v_l_148_; lean_object* v_r_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_803_; 
v_k_146_ = lean_ctor_get(v_t_145_, 1);
v_v_147_ = lean_ctor_get(v_t_145_, 2);
v_l_148_ = lean_ctor_get(v_t_145_, 3);
v_r_149_ = lean_ctor_get(v_t_145_, 4);
v_isSharedCheck_803_ = !lean_is_exclusive(v_t_145_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v_t_145_, 0);
lean_dec(v_unused_804_);
v___x_151_ = v_t_145_;
v_isShared_152_ = v_isSharedCheck_803_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_r_149_);
lean_inc(v_l_148_);
lean_inc(v_v_147_);
lean_inc(v_k_146_);
lean_dec(v_t_145_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_803_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
uint8_t v___x_153_; 
v___x_153_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_144_, v_k_146_);
switch(v___x_153_)
{
case 0:
{
lean_object* v_impl_154_; lean_object* v___x_155_; 
v_impl_154_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___redArg(v_k_144_, v_l_148_);
v___x_155_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_154_) == 0)
{
if (lean_obj_tag(v_r_149_) == 0)
{
lean_object* v_size_156_; lean_object* v_size_157_; lean_object* v_k_158_; lean_object* v_v_159_; lean_object* v_l_160_; lean_object* v_r_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_size_156_ = lean_ctor_get(v_impl_154_, 0);
v_size_157_ = lean_ctor_get(v_r_149_, 0);
v_k_158_ = lean_ctor_get(v_r_149_, 1);
v_v_159_ = lean_ctor_get(v_r_149_, 2);
v_l_160_ = lean_ctor_get(v_r_149_, 3);
lean_inc(v_l_160_);
v_r_161_ = lean_ctor_get(v_r_149_, 4);
v___x_162_ = lean_unsigned_to_nat(3u);
v___x_163_ = lean_nat_mul(v___x_162_, v_size_156_);
v___x_164_ = lean_nat_dec_lt(v___x_163_, v_size_157_);
lean_dec(v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
lean_dec(v_l_160_);
v___x_165_ = lean_nat_add(v___x_155_, v_size_156_);
v___x_166_ = lean_nat_add(v___x_165_, v_size_157_);
lean_dec(v___x_165_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 3, v_impl_154_);
lean_ctor_set(v___x_151_, 0, v___x_166_);
v___x_168_ = v___x_151_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v_impl_154_);
lean_ctor_set(v_reuseFailAlloc_169_, 4, v_r_149_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
else
{
lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_233_; 
lean_inc(v_r_161_);
lean_inc(v_v_159_);
lean_inc(v_k_158_);
lean_inc(v_size_157_);
v_isSharedCheck_233_ = !lean_is_exclusive(v_r_149_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; lean_object* v_unused_238_; 
v_unused_234_ = lean_ctor_get(v_r_149_, 4);
lean_dec(v_unused_234_);
v_unused_235_ = lean_ctor_get(v_r_149_, 3);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_r_149_, 2);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_r_149_, 1);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_r_149_, 0);
lean_dec(v_unused_238_);
v___x_171_ = v_r_149_;
v_isShared_172_ = v_isSharedCheck_233_;
goto v_resetjp_170_;
}
else
{
lean_dec(v_r_149_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_233_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_size_173_; lean_object* v_k_174_; lean_object* v_v_175_; lean_object* v_l_176_; lean_object* v_r_177_; lean_object* v_size_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_size_173_ = lean_ctor_get(v_l_160_, 0);
v_k_174_ = lean_ctor_get(v_l_160_, 1);
v_v_175_ = lean_ctor_get(v_l_160_, 2);
v_l_176_ = lean_ctor_get(v_l_160_, 3);
v_r_177_ = lean_ctor_get(v_l_160_, 4);
v_size_178_ = lean_ctor_get(v_r_161_, 0);
v___x_179_ = lean_unsigned_to_nat(2u);
v___x_180_ = lean_nat_mul(v___x_179_, v_size_178_);
v___x_181_ = lean_nat_dec_lt(v_size_173_, v___x_180_);
lean_dec(v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_209_; 
lean_inc(v_r_177_);
lean_inc(v_l_176_);
lean_inc(v_v_175_);
lean_inc(v_k_174_);
v_isSharedCheck_209_ = !lean_is_exclusive(v_l_160_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; lean_object* v_unused_211_; lean_object* v_unused_212_; lean_object* v_unused_213_; lean_object* v_unused_214_; 
v_unused_210_ = lean_ctor_get(v_l_160_, 4);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_l_160_, 3);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_l_160_, 2);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_l_160_, 1);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_l_160_, 0);
lean_dec(v_unused_214_);
v___x_183_ = v_l_160_;
v_isShared_184_ = v_isSharedCheck_209_;
goto v_resetjp_182_;
}
else
{
lean_dec(v_l_160_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_209_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v___y_199_; 
v___x_185_ = lean_nat_add(v___x_155_, v_size_156_);
v___x_186_ = lean_nat_add(v___x_185_, v_size_157_);
lean_dec(v_size_157_);
if (lean_obj_tag(v_l_176_) == 0)
{
lean_object* v_size_207_; 
v_size_207_ = lean_ctor_get(v_l_176_, 0);
lean_inc(v_size_207_);
v___y_199_ = v_size_207_;
goto v___jp_198_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___y_199_ = v___x_208_;
goto v___jp_198_;
}
v___jp_187_:
{
lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_191_ = lean_nat_add(v___y_188_, v___y_190_);
lean_dec(v___y_190_);
lean_dec(v___y_188_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v_r_161_);
lean_ctor_set(v___x_183_, 3, v_r_177_);
lean_ctor_set(v___x_183_, 2, v_v_159_);
lean_ctor_set(v___x_183_, 1, v_k_158_);
lean_ctor_set(v___x_183_, 0, v___x_191_);
v___x_193_ = v___x_183_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_k_158_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_v_159_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v_r_177_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v_r_161_);
v___x_193_ = v_reuseFailAlloc_197_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 4, v___x_193_);
lean_ctor_set(v___x_171_, 3, v___y_189_);
lean_ctor_set(v___x_171_, 2, v_v_175_);
lean_ctor_set(v___x_171_, 1, v_k_174_);
lean_ctor_set(v___x_171_, 0, v___x_186_);
v___x_195_ = v___x_171_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_k_174_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_v_175_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v___y_189_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
v___jp_198_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_nat_add(v___x_185_, v___y_199_);
lean_dec(v___y_199_);
lean_dec(v___x_185_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v_l_176_);
lean_ctor_set(v___x_151_, 3, v_impl_154_);
lean_ctor_set(v___x_151_, 0, v___x_200_);
v___x_202_ = v___x_151_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v_impl_154_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v_l_176_);
v___x_202_ = v_reuseFailAlloc_206_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; 
v___x_203_ = lean_nat_add(v___x_155_, v_size_178_);
if (lean_obj_tag(v_r_177_) == 0)
{
lean_object* v_size_204_; 
v_size_204_ = lean_ctor_get(v_r_177_, 0);
lean_inc(v_size_204_);
v___y_188_ = v___x_203_;
v___y_189_ = v___x_202_;
v___y_190_ = v_size_204_;
goto v___jp_187_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___y_188_ = v___x_203_;
v___y_189_ = v___x_202_;
v___y_190_ = v___x_205_;
goto v___jp_187_;
}
}
}
}
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
lean_del_object(v___x_151_);
v___x_215_ = lean_nat_add(v___x_155_, v_size_156_);
v___x_216_ = lean_nat_add(v___x_215_, v_size_157_);
lean_dec(v_size_157_);
v___x_217_ = lean_nat_add(v___x_215_, v_size_173_);
lean_dec(v___x_215_);
lean_inc_ref(v_impl_154_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 4, v_l_160_);
lean_ctor_set(v___x_171_, 3, v_impl_154_);
lean_ctor_set(v___x_171_, 2, v_v_147_);
lean_ctor_set(v___x_171_, 1, v_k_146_);
lean_ctor_set(v___x_171_, 0, v___x_217_);
v___x_219_ = v___x_171_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_232_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_232_, 3, v_impl_154_);
lean_ctor_set(v_reuseFailAlloc_232_, 4, v_l_160_);
v___x_219_ = v_reuseFailAlloc_232_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
v_isSharedCheck_226_ = !lean_is_exclusive(v_impl_154_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; lean_object* v_unused_228_; lean_object* v_unused_229_; lean_object* v_unused_230_; lean_object* v_unused_231_; 
v_unused_227_ = lean_ctor_get(v_impl_154_, 4);
lean_dec(v_unused_227_);
v_unused_228_ = lean_ctor_get(v_impl_154_, 3);
lean_dec(v_unused_228_);
v_unused_229_ = lean_ctor_get(v_impl_154_, 2);
lean_dec(v_unused_229_);
v_unused_230_ = lean_ctor_get(v_impl_154_, 1);
lean_dec(v_unused_230_);
v_unused_231_ = lean_ctor_get(v_impl_154_, 0);
lean_dec(v_unused_231_);
v___x_221_ = v_impl_154_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_dec(v_impl_154_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 4, v_r_161_);
lean_ctor_set(v___x_221_, 3, v___x_219_);
lean_ctor_set(v___x_221_, 2, v_v_159_);
lean_ctor_set(v___x_221_, 1, v_k_158_);
lean_ctor_set(v___x_221_, 0, v___x_216_);
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_k_158_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_v_159_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v_r_161_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v_size_239_ = lean_ctor_get(v_impl_154_, 0);
v___x_240_ = lean_nat_add(v___x_155_, v_size_239_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 3, v_impl_154_);
lean_ctor_set(v___x_151_, 0, v___x_240_);
v___x_242_ = v___x_151_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_impl_154_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_r_149_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
if (lean_obj_tag(v_r_149_) == 0)
{
lean_object* v_l_244_; 
v_l_244_ = lean_ctor_get(v_r_149_, 3);
lean_inc(v_l_244_);
if (lean_obj_tag(v_l_244_) == 0)
{
lean_object* v_r_245_; 
v_r_245_ = lean_ctor_get(v_r_149_, 4);
lean_inc(v_r_245_);
if (lean_obj_tag(v_r_245_) == 0)
{
lean_object* v_size_246_; lean_object* v_k_247_; lean_object* v_v_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_261_; 
v_size_246_ = lean_ctor_get(v_r_149_, 0);
v_k_247_ = lean_ctor_get(v_r_149_, 1);
v_v_248_ = lean_ctor_get(v_r_149_, 2);
v_isSharedCheck_261_ = !lean_is_exclusive(v_r_149_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_262_ = lean_ctor_get(v_r_149_, 4);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_r_149_, 3);
lean_dec(v_unused_263_);
v___x_250_ = v_r_149_;
v_isShared_251_ = v_isSharedCheck_261_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_v_248_);
lean_inc(v_k_247_);
lean_inc(v_size_246_);
lean_dec(v_r_149_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_261_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v_size_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v_size_252_ = lean_ctor_get(v_l_244_, 0);
v___x_253_ = lean_nat_add(v___x_155_, v_size_246_);
lean_dec(v_size_246_);
v___x_254_ = lean_nat_add(v___x_155_, v_size_252_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 4, v_l_244_);
lean_ctor_set(v___x_250_, 3, v_impl_154_);
lean_ctor_set(v___x_250_, 2, v_v_147_);
lean_ctor_set(v___x_250_, 1, v_k_146_);
lean_ctor_set(v___x_250_, 0, v___x_254_);
v___x_256_ = v___x_250_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_impl_154_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_l_244_);
v___x_256_ = v_reuseFailAlloc_260_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v_r_245_);
lean_ctor_set(v___x_151_, 3, v___x_256_);
lean_ctor_set(v___x_151_, 2, v_v_248_);
lean_ctor_set(v___x_151_, 1, v_k_247_);
lean_ctor_set(v___x_151_, 0, v___x_253_);
v___x_258_ = v___x_151_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_k_247_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_v_248_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v_r_245_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_k_264_; lean_object* v_v_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_288_; 
v_k_264_ = lean_ctor_get(v_r_149_, 1);
v_v_265_ = lean_ctor_get(v_r_149_, 2);
v_isSharedCheck_288_ = !lean_is_exclusive(v_r_149_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; 
v_unused_289_ = lean_ctor_get(v_r_149_, 4);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_r_149_, 3);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_r_149_, 0);
lean_dec(v_unused_291_);
v___x_267_ = v_r_149_;
v_isShared_268_ = v_isSharedCheck_288_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_v_265_);
lean_inc(v_k_264_);
lean_dec(v_r_149_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_288_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v_k_269_; lean_object* v_v_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_284_; 
v_k_269_ = lean_ctor_get(v_l_244_, 1);
v_v_270_ = lean_ctor_get(v_l_244_, 2);
v_isSharedCheck_284_ = !lean_is_exclusive(v_l_244_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; 
v_unused_285_ = lean_ctor_get(v_l_244_, 4);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_l_244_, 3);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_l_244_, 0);
lean_dec(v_unused_287_);
v___x_272_ = v_l_244_;
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_v_270_);
lean_inc(v_k_269_);
lean_dec(v_l_244_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_284_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = lean_unsigned_to_nat(3u);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 4, v_r_245_);
lean_ctor_set(v___x_272_, 3, v_r_245_);
lean_ctor_set(v___x_272_, 2, v_v_147_);
lean_ctor_set(v___x_272_, 1, v_k_146_);
lean_ctor_set(v___x_272_, 0, v___x_155_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_r_245_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_r_245_);
v___x_276_ = v_reuseFailAlloc_283_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 3, v_r_245_);
lean_ctor_set(v___x_267_, 0, v___x_155_);
v___x_278_ = v___x_267_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_k_264_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_v_265_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v_r_245_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v_r_245_);
v___x_278_ = v_reuseFailAlloc_282_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_280_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v___x_278_);
lean_ctor_set(v___x_151_, 3, v___x_276_);
lean_ctor_set(v___x_151_, 2, v_v_270_);
lean_ctor_set(v___x_151_, 1, v_k_269_);
lean_ctor_set(v___x_151_, 0, v___x_274_);
v___x_280_ = v___x_151_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_k_269_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_v_270_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_292_; 
v_r_292_ = lean_ctor_get(v_r_149_, 4);
lean_inc(v_r_292_);
if (lean_obj_tag(v_r_292_) == 0)
{
lean_object* v_k_293_; lean_object* v_v_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_305_; 
v_k_293_ = lean_ctor_get(v_r_149_, 1);
v_v_294_ = lean_ctor_get(v_r_149_, 2);
v_isSharedCheck_305_ = !lean_is_exclusive(v_r_149_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; lean_object* v_unused_307_; lean_object* v_unused_308_; 
v_unused_306_ = lean_ctor_get(v_r_149_, 4);
lean_dec(v_unused_306_);
v_unused_307_ = lean_ctor_get(v_r_149_, 3);
lean_dec(v_unused_307_);
v_unused_308_ = lean_ctor_get(v_r_149_, 0);
lean_dec(v_unused_308_);
v___x_296_ = v_r_149_;
v_isShared_297_ = v_isSharedCheck_305_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_v_294_);
lean_inc(v_k_293_);
lean_dec(v_r_149_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_305_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = lean_unsigned_to_nat(3u);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 4, v_l_244_);
lean_ctor_set(v___x_296_, 2, v_v_147_);
lean_ctor_set(v___x_296_, 1, v_k_146_);
lean_ctor_set(v___x_296_, 0, v___x_155_);
v___x_300_ = v___x_296_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_l_244_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v_l_244_);
v___x_300_ = v_reuseFailAlloc_304_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v_r_292_);
lean_ctor_set(v___x_151_, 3, v___x_300_);
lean_ctor_set(v___x_151_, 2, v_v_294_);
lean_ctor_set(v___x_151_, 1, v_k_293_);
lean_ctor_set(v___x_151_, 0, v___x_298_);
v___x_302_ = v___x_151_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_k_293_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_v_294_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_r_292_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
else
{
lean_object* v_size_309_; lean_object* v_k_310_; lean_object* v_v_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_322_; 
v_size_309_ = lean_ctor_get(v_r_149_, 0);
v_k_310_ = lean_ctor_get(v_r_149_, 1);
v_v_311_ = lean_ctor_get(v_r_149_, 2);
v_isSharedCheck_322_ = !lean_is_exclusive(v_r_149_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; lean_object* v_unused_324_; 
v_unused_323_ = lean_ctor_get(v_r_149_, 4);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_r_149_, 3);
lean_dec(v_unused_324_);
v___x_313_ = v_r_149_;
v_isShared_314_ = v_isSharedCheck_322_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_v_311_);
lean_inc(v_k_310_);
lean_inc(v_size_309_);
lean_dec(v_r_149_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_322_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 3, v_r_292_);
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_size_309_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_k_310_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_v_311_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v_r_292_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v_r_292_);
v___x_316_ = v_reuseFailAlloc_321_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_unsigned_to_nat(2u);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v___x_316_);
lean_ctor_set(v___x_151_, 3, v_r_292_);
lean_ctor_set(v___x_151_, 0, v___x_317_);
v___x_319_ = v___x_151_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_r_292_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v___x_316_);
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
}
}
else
{
lean_object* v___x_326_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 3, v_r_149_);
lean_ctor_set(v___x_151_, 0, v___x_155_);
v___x_326_ = v___x_151_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_r_149_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_r_149_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
case 1:
{
lean_del_object(v___x_151_);
lean_dec(v_v_147_);
lean_dec(v_k_146_);
if (lean_obj_tag(v_l_148_) == 0)
{
if (lean_obj_tag(v_r_149_) == 0)
{
lean_object* v_size_328_; lean_object* v_k_329_; lean_object* v_v_330_; lean_object* v_l_331_; lean_object* v_r_332_; lean_object* v_size_333_; lean_object* v_k_334_; lean_object* v_v_335_; lean_object* v_l_336_; lean_object* v_r_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_size_328_ = lean_ctor_get(v_l_148_, 0);
v_k_329_ = lean_ctor_get(v_l_148_, 1);
v_v_330_ = lean_ctor_get(v_l_148_, 2);
v_l_331_ = lean_ctor_get(v_l_148_, 3);
v_r_332_ = lean_ctor_get(v_l_148_, 4);
lean_inc(v_r_332_);
v_size_333_ = lean_ctor_get(v_r_149_, 0);
v_k_334_ = lean_ctor_get(v_r_149_, 1);
v_v_335_ = lean_ctor_get(v_r_149_, 2);
v_l_336_ = lean_ctor_get(v_r_149_, 3);
lean_inc(v_l_336_);
v_r_337_ = lean_ctor_get(v_r_149_, 4);
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_dec_lt(v_size_328_, v_size_333_);
if (v___x_339_ == 0)
{
lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_475_; 
lean_inc(v_l_331_);
lean_inc(v_v_330_);
lean_inc(v_k_329_);
v_isSharedCheck_475_ = !lean_is_exclusive(v_l_148_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; lean_object* v_unused_480_; 
v_unused_476_ = lean_ctor_get(v_l_148_, 4);
lean_dec(v_unused_476_);
v_unused_477_ = lean_ctor_get(v_l_148_, 3);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_l_148_, 2);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_l_148_, 1);
lean_dec(v_unused_479_);
v_unused_480_ = lean_ctor_get(v_l_148_, 0);
lean_dec(v_unused_480_);
v___x_341_ = v_l_148_;
v_isShared_342_ = v_isSharedCheck_475_;
goto v_resetjp_340_;
}
else
{
lean_dec(v_l_148_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_475_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v_tree_344_; 
v___x_343_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_329_, v_v_330_, v_l_331_, v_r_332_);
v_tree_344_ = lean_ctor_get(v___x_343_, 2);
if (lean_obj_tag(v_tree_344_) == 0)
{
lean_object* v_k_345_; lean_object* v_v_346_; lean_object* v_size_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
lean_inc_ref(v_tree_344_);
v_k_345_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_k_345_);
v_v_346_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_v_346_);
lean_dec_ref(v___x_343_);
v_size_347_ = lean_ctor_get(v_tree_344_, 0);
v___x_348_ = lean_unsigned_to_nat(3u);
v___x_349_ = lean_nat_mul(v___x_348_, v_size_347_);
v___x_350_ = lean_nat_dec_lt(v___x_349_, v_size_333_);
lean_dec(v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
lean_dec(v_l_336_);
v___x_351_ = lean_nat_add(v___x_338_, v_size_347_);
v___x_352_ = lean_nat_add(v___x_351_, v_size_333_);
lean_dec(v___x_351_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v_r_149_);
lean_ctor_set(v___x_341_, 3, v_tree_344_);
lean_ctor_set(v___x_341_, 2, v_v_346_);
lean_ctor_set(v___x_341_, 1, v_k_345_);
lean_ctor_set(v___x_341_, 0, v___x_352_);
v___x_354_ = v___x_341_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_k_345_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_v_346_);
lean_ctor_set(v_reuseFailAlloc_355_, 3, v_tree_344_);
lean_ctor_set(v_reuseFailAlloc_355_, 4, v_r_149_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
else
{
lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_410_; 
lean_inc(v_r_337_);
lean_inc(v_v_335_);
lean_inc(v_k_334_);
lean_inc(v_size_333_);
v_isSharedCheck_410_ = !lean_is_exclusive(v_r_149_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; lean_object* v_unused_412_; lean_object* v_unused_413_; lean_object* v_unused_414_; lean_object* v_unused_415_; 
v_unused_411_ = lean_ctor_get(v_r_149_, 4);
lean_dec(v_unused_411_);
v_unused_412_ = lean_ctor_get(v_r_149_, 3);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_r_149_, 2);
lean_dec(v_unused_413_);
v_unused_414_ = lean_ctor_get(v_r_149_, 1);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_r_149_, 0);
lean_dec(v_unused_415_);
v___x_357_ = v_r_149_;
v_isShared_358_ = v_isSharedCheck_410_;
goto v_resetjp_356_;
}
else
{
lean_dec(v_r_149_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_410_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v_size_359_; lean_object* v_k_360_; lean_object* v_v_361_; lean_object* v_l_362_; lean_object* v_r_363_; lean_object* v_size_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_size_359_ = lean_ctor_get(v_l_336_, 0);
v_k_360_ = lean_ctor_get(v_l_336_, 1);
v_v_361_ = lean_ctor_get(v_l_336_, 2);
v_l_362_ = lean_ctor_get(v_l_336_, 3);
v_r_363_ = lean_ctor_get(v_l_336_, 4);
v_size_364_ = lean_ctor_get(v_r_337_, 0);
v___x_365_ = lean_unsigned_to_nat(2u);
v___x_366_ = lean_nat_mul(v___x_365_, v_size_364_);
v___x_367_ = lean_nat_dec_lt(v_size_359_, v___x_366_);
lean_dec(v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_395_; 
lean_inc(v_r_363_);
lean_inc(v_l_362_);
lean_inc(v_v_361_);
lean_inc(v_k_360_);
v_isSharedCheck_395_ = !lean_is_exclusive(v_l_336_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; lean_object* v_unused_397_; lean_object* v_unused_398_; lean_object* v_unused_399_; lean_object* v_unused_400_; 
v_unused_396_ = lean_ctor_get(v_l_336_, 4);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_l_336_, 3);
lean_dec(v_unused_397_);
v_unused_398_ = lean_ctor_get(v_l_336_, 2);
lean_dec(v_unused_398_);
v_unused_399_ = lean_ctor_get(v_l_336_, 1);
lean_dec(v_unused_399_);
v_unused_400_ = lean_ctor_get(v_l_336_, 0);
lean_dec(v_unused_400_);
v___x_369_ = v_l_336_;
v_isShared_370_ = v_isSharedCheck_395_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_l_336_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_395_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_385_; 
v___x_371_ = lean_nat_add(v___x_338_, v_size_347_);
v___x_372_ = lean_nat_add(v___x_371_, v_size_333_);
lean_dec(v_size_333_);
if (lean_obj_tag(v_l_362_) == 0)
{
lean_object* v_size_393_; 
v_size_393_ = lean_ctor_get(v_l_362_, 0);
lean_inc(v_size_393_);
v___y_385_ = v_size_393_;
goto v___jp_384_;
}
else
{
lean_object* v___x_394_; 
v___x_394_ = lean_unsigned_to_nat(0u);
v___y_385_ = v___x_394_;
goto v___jp_384_;
}
v___jp_373_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_nat_add(v___y_374_, v___y_376_);
lean_dec(v___y_376_);
lean_dec(v___y_374_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 4, v_r_337_);
lean_ctor_set(v___x_369_, 3, v_r_363_);
lean_ctor_set(v___x_369_, 2, v_v_335_);
lean_ctor_set(v___x_369_, 1, v_k_334_);
lean_ctor_set(v___x_369_, 0, v___x_377_);
v___x_379_ = v___x_369_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_k_334_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_v_335_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_r_363_);
lean_ctor_set(v_reuseFailAlloc_383_, 4, v_r_337_);
v___x_379_ = v_reuseFailAlloc_383_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_381_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 4, v___x_379_);
lean_ctor_set(v___x_357_, 3, v___y_375_);
lean_ctor_set(v___x_357_, 2, v_v_361_);
lean_ctor_set(v___x_357_, 1, v_k_360_);
lean_ctor_set(v___x_357_, 0, v___x_372_);
v___x_381_ = v___x_357_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_k_360_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_v_361_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v___y_375_);
lean_ctor_set(v_reuseFailAlloc_382_, 4, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
v___jp_384_:
{
lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_386_ = lean_nat_add(v___x_371_, v___y_385_);
lean_dec(v___y_385_);
lean_dec(v___x_371_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v_l_362_);
lean_ctor_set(v___x_341_, 3, v_tree_344_);
lean_ctor_set(v___x_341_, 2, v_v_346_);
lean_ctor_set(v___x_341_, 1, v_k_345_);
lean_ctor_set(v___x_341_, 0, v___x_386_);
v___x_388_ = v___x_341_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_k_345_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_v_346_);
lean_ctor_set(v_reuseFailAlloc_392_, 3, v_tree_344_);
lean_ctor_set(v_reuseFailAlloc_392_, 4, v_l_362_);
v___x_388_ = v_reuseFailAlloc_392_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; 
v___x_389_ = lean_nat_add(v___x_338_, v_size_364_);
if (lean_obj_tag(v_r_363_) == 0)
{
lean_object* v_size_390_; 
v_size_390_ = lean_ctor_get(v_r_363_, 0);
lean_inc(v_size_390_);
v___y_374_ = v___x_389_;
v___y_375_ = v___x_388_;
v___y_376_ = v_size_390_;
goto v___jp_373_;
}
else
{
lean_object* v___x_391_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___y_374_ = v___x_389_;
v___y_375_ = v___x_388_;
v___y_376_ = v___x_391_;
goto v___jp_373_;
}
}
}
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_401_ = lean_nat_add(v___x_338_, v_size_347_);
v___x_402_ = lean_nat_add(v___x_401_, v_size_333_);
lean_dec(v_size_333_);
v___x_403_ = lean_nat_add(v___x_401_, v_size_359_);
lean_dec(v___x_401_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 4, v_l_336_);
lean_ctor_set(v___x_357_, 3, v_tree_344_);
lean_ctor_set(v___x_357_, 2, v_v_346_);
lean_ctor_set(v___x_357_, 1, v_k_345_);
lean_ctor_set(v___x_357_, 0, v___x_403_);
v___x_405_ = v___x_357_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_k_345_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_v_346_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_tree_344_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_l_336_);
v___x_405_ = v_reuseFailAlloc_409_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v_r_337_);
lean_ctor_set(v___x_341_, 3, v___x_405_);
lean_ctor_set(v___x_341_, 2, v_v_335_);
lean_ctor_set(v___x_341_, 1, v_k_334_);
lean_ctor_set(v___x_341_, 0, v___x_402_);
v___x_407_ = v___x_341_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_k_334_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_v_335_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_r_337_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
}
else
{
lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_469_; 
lean_inc(v_r_337_);
lean_inc(v_v_335_);
lean_inc(v_k_334_);
lean_inc(v_size_333_);
v_isSharedCheck_469_ = !lean_is_exclusive(v_r_149_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; lean_object* v_unused_474_; 
v_unused_470_ = lean_ctor_get(v_r_149_, 4);
lean_dec(v_unused_470_);
v_unused_471_ = lean_ctor_get(v_r_149_, 3);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_r_149_, 2);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_r_149_, 1);
lean_dec(v_unused_473_);
v_unused_474_ = lean_ctor_get(v_r_149_, 0);
lean_dec(v_unused_474_);
v___x_417_ = v_r_149_;
v_isShared_418_ = v_isSharedCheck_469_;
goto v_resetjp_416_;
}
else
{
lean_dec(v_r_149_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_469_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
if (lean_obj_tag(v_l_336_) == 0)
{
if (lean_obj_tag(v_r_337_) == 0)
{
lean_object* v_k_419_; lean_object* v_v_420_; lean_object* v_size_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
lean_inc(v_tree_344_);
v_k_419_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_k_419_);
v_v_420_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_v_420_);
lean_dec_ref(v___x_343_);
v_size_421_ = lean_ctor_get(v_l_336_, 0);
v___x_422_ = lean_nat_add(v___x_338_, v_size_333_);
lean_dec(v_size_333_);
v___x_423_ = lean_nat_add(v___x_338_, v_size_421_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v_l_336_);
lean_ctor_set(v___x_417_, 3, v_tree_344_);
lean_ctor_set(v___x_417_, 2, v_v_420_);
lean_ctor_set(v___x_417_, 1, v_k_419_);
lean_ctor_set(v___x_417_, 0, v___x_423_);
v___x_425_ = v___x_417_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_k_419_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_v_420_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_tree_344_);
lean_ctor_set(v_reuseFailAlloc_429_, 4, v_l_336_);
v___x_425_ = v_reuseFailAlloc_429_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v_r_337_);
lean_ctor_set(v___x_341_, 3, v___x_425_);
lean_ctor_set(v___x_341_, 2, v_v_335_);
lean_ctor_set(v___x_341_, 1, v_k_334_);
lean_ctor_set(v___x_341_, 0, v___x_422_);
v___x_427_ = v___x_341_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_k_334_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_v_335_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_r_337_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v_k_430_; lean_object* v_v_431_; lean_object* v_k_432_; lean_object* v_v_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_447_; 
lean_dec(v_size_333_);
v_k_430_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_k_430_);
v_v_431_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_v_431_);
lean_dec_ref(v___x_343_);
v_k_432_ = lean_ctor_get(v_l_336_, 1);
v_v_433_ = lean_ctor_get(v_l_336_, 2);
v_isSharedCheck_447_ = !lean_is_exclusive(v_l_336_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_448_ = lean_ctor_get(v_l_336_, 4);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_l_336_, 3);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_l_336_, 0);
lean_dec(v_unused_450_);
v___x_435_ = v_l_336_;
v_isShared_436_ = v_isSharedCheck_447_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_v_433_);
lean_inc(v_k_432_);
lean_dec(v_l_336_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_447_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = lean_unsigned_to_nat(3u);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 4, v_r_337_);
lean_ctor_set(v___x_435_, 3, v_r_337_);
lean_ctor_set(v___x_435_, 2, v_v_431_);
lean_ctor_set(v___x_435_, 1, v_k_430_);
lean_ctor_set(v___x_435_, 0, v___x_338_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_k_430_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_v_431_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_r_337_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v_r_337_);
v___x_439_ = v_reuseFailAlloc_446_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_441_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 3, v_r_337_);
lean_ctor_set(v___x_417_, 0, v___x_338_);
v___x_441_ = v___x_417_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_k_334_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_v_335_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_r_337_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v_r_337_);
v___x_441_ = v_reuseFailAlloc_445_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_443_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v___x_441_);
lean_ctor_set(v___x_341_, 3, v___x_439_);
lean_ctor_set(v___x_341_, 2, v_v_433_);
lean_ctor_set(v___x_341_, 1, v_k_432_);
lean_ctor_set(v___x_341_, 0, v___x_437_);
v___x_443_ = v___x_341_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_k_432_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_v_433_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_337_) == 0)
{
lean_object* v_k_451_; lean_object* v_v_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
lean_dec(v_size_333_);
v_k_451_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_k_451_);
v_v_452_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_v_452_);
lean_dec_ref(v___x_343_);
v___x_453_ = lean_unsigned_to_nat(3u);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 4, v_l_336_);
lean_ctor_set(v___x_417_, 2, v_v_452_);
lean_ctor_set(v___x_417_, 1, v_k_451_);
lean_ctor_set(v___x_417_, 0, v___x_338_);
v___x_455_ = v___x_417_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_k_451_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_v_452_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_l_336_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_l_336_);
v___x_455_ = v_reuseFailAlloc_459_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v_r_337_);
lean_ctor_set(v___x_341_, 3, v___x_455_);
lean_ctor_set(v___x_341_, 2, v_v_335_);
lean_ctor_set(v___x_341_, 1, v_k_334_);
lean_ctor_set(v___x_341_, 0, v___x_453_);
v___x_457_ = v___x_341_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_k_334_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_v_335_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_458_, 4, v_r_337_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
else
{
lean_object* v_k_460_; lean_object* v_v_461_; lean_object* v___x_463_; 
v_k_460_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_k_460_);
v_v_461_ = lean_ctor_get(v___x_343_, 1);
lean_inc(v_v_461_);
lean_dec_ref(v___x_343_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 3, v_r_337_);
v___x_463_ = v___x_417_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_size_333_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_k_334_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_v_335_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_r_337_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_r_337_);
v___x_463_ = v_reuseFailAlloc_468_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_unsigned_to_nat(2u);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v___x_463_);
lean_ctor_set(v___x_341_, 3, v_r_337_);
lean_ctor_set(v___x_341_, 2, v_v_461_);
lean_ctor_set(v___x_341_, 1, v_k_460_);
lean_ctor_set(v___x_341_, 0, v___x_464_);
v___x_466_ = v___x_341_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_k_460_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_v_461_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v_r_337_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v___x_463_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_633_; 
lean_inc(v_r_337_);
lean_inc(v_v_335_);
lean_inc(v_k_334_);
v_isSharedCheck_633_ = !lean_is_exclusive(v_r_149_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; lean_object* v_unused_635_; lean_object* v_unused_636_; lean_object* v_unused_637_; lean_object* v_unused_638_; 
v_unused_634_ = lean_ctor_get(v_r_149_, 4);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_r_149_, 3);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_r_149_, 2);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_r_149_, 1);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_r_149_, 0);
lean_dec(v_unused_638_);
v___x_482_ = v_r_149_;
v_isShared_483_ = v_isSharedCheck_633_;
goto v_resetjp_481_;
}
else
{
lean_dec(v_r_149_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_633_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v_tree_485_; 
v___x_484_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_334_, v_v_335_, v_l_336_, v_r_337_);
v_tree_485_ = lean_ctor_get(v___x_484_, 2);
lean_inc(v_tree_485_);
if (lean_obj_tag(v_tree_485_) == 0)
{
lean_object* v_k_486_; lean_object* v_v_487_; lean_object* v_size_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_k_486_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_k_486_);
v_v_487_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_v_487_);
lean_dec_ref(v___x_484_);
v_size_488_ = lean_ctor_get(v_tree_485_, 0);
v___x_489_ = lean_unsigned_to_nat(3u);
v___x_490_ = lean_nat_mul(v___x_489_, v_size_488_);
v___x_491_ = lean_nat_dec_lt(v___x_490_, v_size_328_);
lean_dec(v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
lean_dec(v_r_332_);
v___x_492_ = lean_nat_add(v___x_338_, v_size_328_);
v___x_493_ = lean_nat_add(v___x_492_, v_size_488_);
lean_dec(v___x_492_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 4, v_tree_485_);
lean_ctor_set(v___x_482_, 3, v_l_148_);
lean_ctor_set(v___x_482_, 2, v_v_487_);
lean_ctor_set(v___x_482_, 1, v_k_486_);
lean_ctor_set(v___x_482_, 0, v___x_493_);
v___x_495_ = v___x_482_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_k_486_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_v_487_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_l_148_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_tree_485_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_562_; 
lean_inc(v_l_331_);
lean_inc(v_v_330_);
lean_inc(v_k_329_);
lean_inc(v_size_328_);
v_isSharedCheck_562_ = !lean_is_exclusive(v_l_148_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; lean_object* v_unused_564_; lean_object* v_unused_565_; lean_object* v_unused_566_; lean_object* v_unused_567_; 
v_unused_563_ = lean_ctor_get(v_l_148_, 4);
lean_dec(v_unused_563_);
v_unused_564_ = lean_ctor_get(v_l_148_, 3);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_l_148_, 2);
lean_dec(v_unused_565_);
v_unused_566_ = lean_ctor_get(v_l_148_, 1);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_l_148_, 0);
lean_dec(v_unused_567_);
v___x_498_ = v_l_148_;
v_isShared_499_ = v_isSharedCheck_562_;
goto v_resetjp_497_;
}
else
{
lean_dec(v_l_148_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_562_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v_size_500_; lean_object* v_size_501_; lean_object* v_k_502_; lean_object* v_v_503_; lean_object* v_l_504_; lean_object* v_r_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_size_500_ = lean_ctor_get(v_l_331_, 0);
v_size_501_ = lean_ctor_get(v_r_332_, 0);
v_k_502_ = lean_ctor_get(v_r_332_, 1);
v_v_503_ = lean_ctor_get(v_r_332_, 2);
v_l_504_ = lean_ctor_get(v_r_332_, 3);
v_r_505_ = lean_ctor_get(v_r_332_, 4);
v___x_506_ = lean_unsigned_to_nat(2u);
v___x_507_ = lean_nat_mul(v___x_506_, v_size_500_);
v___x_508_ = lean_nat_dec_lt(v_size_501_, v___x_507_);
lean_dec(v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_546_; 
lean_inc(v_r_505_);
lean_inc(v_l_504_);
lean_inc(v_v_503_);
lean_inc(v_k_502_);
lean_del_object(v___x_498_);
v_isSharedCheck_546_ = !lean_is_exclusive(v_r_332_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; lean_object* v_unused_551_; 
v_unused_547_ = lean_ctor_get(v_r_332_, 4);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_r_332_, 3);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_r_332_, 2);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_r_332_, 1);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_r_332_, 0);
lean_dec(v_unused_551_);
v___x_510_ = v_r_332_;
v_isShared_511_ = v_isSharedCheck_546_;
goto v_resetjp_509_;
}
else
{
lean_dec(v_r_332_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_546_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___x_534_; lean_object* v___y_536_; 
v___x_512_ = lean_nat_add(v___x_338_, v_size_328_);
lean_dec(v_size_328_);
v___x_513_ = lean_nat_add(v___x_512_, v_size_488_);
lean_dec(v___x_512_);
v___x_534_ = lean_nat_add(v___x_338_, v_size_500_);
if (lean_obj_tag(v_l_504_) == 0)
{
lean_object* v_size_544_; 
v_size_544_ = lean_ctor_get(v_l_504_, 0);
lean_inc(v_size_544_);
v___y_536_ = v_size_544_;
goto v___jp_535_;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___y_536_ = v___x_545_;
goto v___jp_535_;
}
v___jp_514_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
v___x_518_ = lean_nat_add(v___y_515_, v___y_517_);
lean_dec(v___y_517_);
lean_dec(v___y_515_);
lean_inc_ref(v_tree_485_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 4, v_tree_485_);
lean_ctor_set(v___x_510_, 3, v_r_505_);
lean_ctor_set(v___x_510_, 2, v_v_487_);
lean_ctor_set(v___x_510_, 1, v_k_486_);
lean_ctor_set(v___x_510_, 0, v___x_518_);
v___x_520_ = v___x_510_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_k_486_);
lean_ctor_set(v_reuseFailAlloc_533_, 2, v_v_487_);
lean_ctor_set(v_reuseFailAlloc_533_, 3, v_r_505_);
lean_ctor_set(v_reuseFailAlloc_533_, 4, v_tree_485_);
v___x_520_ = v_reuseFailAlloc_533_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_isSharedCheck_527_ = !lean_is_exclusive(v_tree_485_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; lean_object* v_unused_529_; lean_object* v_unused_530_; lean_object* v_unused_531_; lean_object* v_unused_532_; 
v_unused_528_ = lean_ctor_get(v_tree_485_, 4);
lean_dec(v_unused_528_);
v_unused_529_ = lean_ctor_get(v_tree_485_, 3);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_tree_485_, 2);
lean_dec(v_unused_530_);
v_unused_531_ = lean_ctor_get(v_tree_485_, 1);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_tree_485_, 0);
lean_dec(v_unused_532_);
v___x_522_ = v_tree_485_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_dec(v_tree_485_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 4, v___x_520_);
lean_ctor_set(v___x_522_, 3, v___y_516_);
lean_ctor_set(v___x_522_, 2, v_v_503_);
lean_ctor_set(v___x_522_, 1, v_k_502_);
lean_ctor_set(v___x_522_, 0, v___x_513_);
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_k_502_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_v_503_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v___y_516_);
lean_ctor_set(v_reuseFailAlloc_526_, 4, v___x_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
v___jp_535_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_nat_add(v___x_534_, v___y_536_);
lean_dec(v___y_536_);
lean_dec(v___x_534_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 4, v_l_504_);
lean_ctor_set(v___x_482_, 3, v_l_331_);
lean_ctor_set(v___x_482_, 2, v_v_330_);
lean_ctor_set(v___x_482_, 1, v_k_329_);
lean_ctor_set(v___x_482_, 0, v___x_537_);
v___x_539_ = v___x_482_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_k_329_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_v_330_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v_l_331_);
lean_ctor_set(v_reuseFailAlloc_543_, 4, v_l_504_);
v___x_539_ = v_reuseFailAlloc_543_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; 
v___x_540_ = lean_nat_add(v___x_338_, v_size_488_);
if (lean_obj_tag(v_r_505_) == 0)
{
lean_object* v_size_541_; 
v_size_541_ = lean_ctor_get(v_r_505_, 0);
lean_inc(v_size_541_);
v___y_515_ = v___x_540_;
v___y_516_ = v___x_539_;
v___y_517_ = v_size_541_;
goto v___jp_514_;
}
else
{
lean_object* v___x_542_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___y_515_ = v___x_540_;
v___y_516_ = v___x_539_;
v___y_517_ = v___x_542_;
goto v___jp_514_;
}
}
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_552_ = lean_nat_add(v___x_338_, v_size_328_);
lean_dec(v_size_328_);
v___x_553_ = lean_nat_add(v___x_552_, v_size_488_);
lean_dec(v___x_552_);
v___x_554_ = lean_nat_add(v___x_338_, v_size_488_);
v___x_555_ = lean_nat_add(v___x_554_, v_size_501_);
lean_dec(v___x_554_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 4, v_tree_485_);
lean_ctor_set(v___x_482_, 3, v_r_332_);
lean_ctor_set(v___x_482_, 2, v_v_487_);
lean_ctor_set(v___x_482_, 1, v_k_486_);
lean_ctor_set(v___x_482_, 0, v___x_555_);
v___x_557_ = v___x_482_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_k_486_);
lean_ctor_set(v_reuseFailAlloc_561_, 2, v_v_487_);
lean_ctor_set(v_reuseFailAlloc_561_, 3, v_r_332_);
lean_ctor_set(v_reuseFailAlloc_561_, 4, v_tree_485_);
v___x_557_ = v_reuseFailAlloc_561_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 4, v___x_557_);
lean_ctor_set(v___x_498_, 0, v___x_553_);
v___x_559_ = v___x_498_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_k_329_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_v_330_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_l_331_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_331_) == 0)
{
lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_591_; 
lean_inc_ref(v_l_331_);
lean_inc(v_v_330_);
lean_inc(v_k_329_);
lean_inc(v_size_328_);
v_isSharedCheck_591_ = !lean_is_exclusive(v_l_148_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; lean_object* v_unused_593_; lean_object* v_unused_594_; lean_object* v_unused_595_; lean_object* v_unused_596_; 
v_unused_592_ = lean_ctor_get(v_l_148_, 4);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_l_148_, 3);
lean_dec(v_unused_593_);
v_unused_594_ = lean_ctor_get(v_l_148_, 2);
lean_dec(v_unused_594_);
v_unused_595_ = lean_ctor_get(v_l_148_, 1);
lean_dec(v_unused_595_);
v_unused_596_ = lean_ctor_get(v_l_148_, 0);
lean_dec(v_unused_596_);
v___x_569_ = v_l_148_;
v_isShared_570_ = v_isSharedCheck_591_;
goto v_resetjp_568_;
}
else
{
lean_dec(v_l_148_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_591_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
if (lean_obj_tag(v_r_332_) == 0)
{
lean_object* v_k_571_; lean_object* v_v_572_; lean_object* v_size_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v_k_571_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_k_571_);
v_v_572_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_v_572_);
lean_dec_ref(v___x_484_);
v_size_573_ = lean_ctor_get(v_r_332_, 0);
v___x_574_ = lean_nat_add(v___x_338_, v_size_328_);
lean_dec(v_size_328_);
v___x_575_ = lean_nat_add(v___x_338_, v_size_573_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 4, v_tree_485_);
lean_ctor_set(v___x_482_, 3, v_r_332_);
lean_ctor_set(v___x_482_, 2, v_v_572_);
lean_ctor_set(v___x_482_, 1, v_k_571_);
lean_ctor_set(v___x_482_, 0, v___x_575_);
v___x_577_ = v___x_482_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_k_571_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_v_572_);
lean_ctor_set(v_reuseFailAlloc_581_, 3, v_r_332_);
lean_ctor_set(v_reuseFailAlloc_581_, 4, v_tree_485_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 4, v___x_577_);
lean_ctor_set(v___x_569_, 0, v___x_574_);
v___x_579_ = v___x_569_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_k_329_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v_v_330_);
lean_ctor_set(v_reuseFailAlloc_580_, 3, v_l_331_);
lean_ctor_set(v_reuseFailAlloc_580_, 4, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
else
{
lean_object* v_k_582_; lean_object* v_v_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
lean_dec(v_size_328_);
v_k_582_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_k_582_);
v_v_583_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_v_583_);
lean_dec_ref(v___x_484_);
v___x_584_ = lean_unsigned_to_nat(3u);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 4, v_r_332_);
lean_ctor_set(v___x_482_, 3, v_r_332_);
lean_ctor_set(v___x_482_, 2, v_v_583_);
lean_ctor_set(v___x_482_, 1, v_k_582_);
lean_ctor_set(v___x_482_, 0, v___x_338_);
v___x_586_ = v___x_482_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_k_582_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_v_583_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_r_332_);
lean_ctor_set(v_reuseFailAlloc_590_, 4, v_r_332_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_588_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 4, v___x_586_);
lean_ctor_set(v___x_569_, 0, v___x_584_);
v___x_588_ = v___x_569_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_k_329_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_v_330_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v_l_331_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_332_) == 0)
{
lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_621_; 
lean_inc(v_l_331_);
lean_inc(v_v_330_);
lean_inc(v_k_329_);
v_isSharedCheck_621_ = !lean_is_exclusive(v_l_148_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; lean_object* v_unused_623_; lean_object* v_unused_624_; lean_object* v_unused_625_; lean_object* v_unused_626_; 
v_unused_622_ = lean_ctor_get(v_l_148_, 4);
lean_dec(v_unused_622_);
v_unused_623_ = lean_ctor_get(v_l_148_, 3);
lean_dec(v_unused_623_);
v_unused_624_ = lean_ctor_get(v_l_148_, 2);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_l_148_, 1);
lean_dec(v_unused_625_);
v_unused_626_ = lean_ctor_get(v_l_148_, 0);
lean_dec(v_unused_626_);
v___x_598_ = v_l_148_;
v_isShared_599_ = v_isSharedCheck_621_;
goto v_resetjp_597_;
}
else
{
lean_dec(v_l_148_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_621_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_k_600_; lean_object* v_v_601_; lean_object* v_k_602_; lean_object* v_v_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_617_; 
v_k_600_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_k_600_);
v_v_601_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_v_601_);
lean_dec_ref(v___x_484_);
v_k_602_ = lean_ctor_get(v_r_332_, 1);
v_v_603_ = lean_ctor_get(v_r_332_, 2);
v_isSharedCheck_617_ = !lean_is_exclusive(v_r_332_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; lean_object* v_unused_619_; lean_object* v_unused_620_; 
v_unused_618_ = lean_ctor_get(v_r_332_, 4);
lean_dec(v_unused_618_);
v_unused_619_ = lean_ctor_get(v_r_332_, 3);
lean_dec(v_unused_619_);
v_unused_620_ = lean_ctor_get(v_r_332_, 0);
lean_dec(v_unused_620_);
v___x_605_ = v_r_332_;
v_isShared_606_ = v_isSharedCheck_617_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_v_603_);
lean_inc(v_k_602_);
lean_dec(v_r_332_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_617_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = lean_unsigned_to_nat(3u);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 4, v_l_331_);
lean_ctor_set(v___x_605_, 3, v_l_331_);
lean_ctor_set(v___x_605_, 2, v_v_330_);
lean_ctor_set(v___x_605_, 1, v_k_329_);
lean_ctor_set(v___x_605_, 0, v___x_338_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_k_329_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_v_330_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_l_331_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_l_331_);
v___x_609_ = v_reuseFailAlloc_616_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 4, v_l_331_);
lean_ctor_set(v___x_482_, 3, v_l_331_);
lean_ctor_set(v___x_482_, 2, v_v_601_);
lean_ctor_set(v___x_482_, 1, v_k_600_);
lean_ctor_set(v___x_482_, 0, v___x_338_);
v___x_611_ = v___x_482_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_k_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_v_601_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_l_331_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_l_331_);
v___x_611_ = v_reuseFailAlloc_615_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 4, v___x_611_);
lean_ctor_set(v___x_598_, 3, v___x_609_);
lean_ctor_set(v___x_598_, 2, v_v_603_);
lean_ctor_set(v___x_598_, 1, v_k_602_);
lean_ctor_set(v___x_598_, 0, v___x_607_);
v___x_613_ = v___x_598_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_v_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
else
{
lean_object* v_k_627_; lean_object* v_v_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v_k_627_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_k_627_);
v_v_628_ = lean_ctor_get(v___x_484_, 1);
lean_inc(v_v_628_);
lean_dec_ref(v___x_484_);
v___x_629_ = lean_unsigned_to_nat(2u);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 4, v_r_332_);
lean_ctor_set(v___x_482_, 3, v_l_148_);
lean_ctor_set(v___x_482_, 2, v_v_628_);
lean_ctor_set(v___x_482_, 1, v_k_627_);
lean_ctor_set(v___x_482_, 0, v___x_629_);
v___x_631_ = v___x_482_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_k_627_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_v_628_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_l_148_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_r_332_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
}
else
{
return v_l_148_;
}
}
else
{
return v_r_149_;
}
}
default: 
{
lean_object* v_impl_639_; lean_object* v___x_640_; 
v_impl_639_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___redArg(v_k_144_, v_r_149_);
v___x_640_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_639_) == 0)
{
if (lean_obj_tag(v_l_148_) == 0)
{
lean_object* v_size_641_; lean_object* v_size_642_; lean_object* v_k_643_; lean_object* v_v_644_; lean_object* v_l_645_; lean_object* v_r_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_size_641_ = lean_ctor_get(v_impl_639_, 0);
v_size_642_ = lean_ctor_get(v_l_148_, 0);
v_k_643_ = lean_ctor_get(v_l_148_, 1);
v_v_644_ = lean_ctor_get(v_l_148_, 2);
v_l_645_ = lean_ctor_get(v_l_148_, 3);
v_r_646_ = lean_ctor_get(v_l_148_, 4);
lean_inc(v_r_646_);
v___x_647_ = lean_unsigned_to_nat(3u);
v___x_648_ = lean_nat_mul(v___x_647_, v_size_641_);
v___x_649_ = lean_nat_dec_lt(v___x_648_, v_size_642_);
lean_dec(v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
lean_dec(v_r_646_);
v___x_650_ = lean_nat_add(v___x_640_, v_size_642_);
v___x_651_ = lean_nat_add(v___x_650_, v_size_641_);
lean_dec(v___x_650_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v_impl_639_);
lean_ctor_set(v___x_151_, 0, v___x_651_);
v___x_653_ = v___x_151_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v_l_148_);
lean_ctor_set(v_reuseFailAlloc_654_, 4, v_impl_639_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_720_; 
lean_inc(v_l_645_);
lean_inc(v_v_644_);
lean_inc(v_k_643_);
lean_inc(v_size_642_);
v_isSharedCheck_720_ = !lean_is_exclusive(v_l_148_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; lean_object* v_unused_722_; lean_object* v_unused_723_; lean_object* v_unused_724_; lean_object* v_unused_725_; 
v_unused_721_ = lean_ctor_get(v_l_148_, 4);
lean_dec(v_unused_721_);
v_unused_722_ = lean_ctor_get(v_l_148_, 3);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_l_148_, 2);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_l_148_, 1);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_l_148_, 0);
lean_dec(v_unused_725_);
v___x_656_ = v_l_148_;
v_isShared_657_ = v_isSharedCheck_720_;
goto v_resetjp_655_;
}
else
{
lean_dec(v_l_148_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_720_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_size_658_; lean_object* v_size_659_; lean_object* v_k_660_; lean_object* v_v_661_; lean_object* v_l_662_; lean_object* v_r_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_size_658_ = lean_ctor_get(v_l_645_, 0);
v_size_659_ = lean_ctor_get(v_r_646_, 0);
v_k_660_ = lean_ctor_get(v_r_646_, 1);
v_v_661_ = lean_ctor_get(v_r_646_, 2);
v_l_662_ = lean_ctor_get(v_r_646_, 3);
v_r_663_ = lean_ctor_get(v_r_646_, 4);
v___x_664_ = lean_unsigned_to_nat(2u);
v___x_665_ = lean_nat_mul(v___x_664_, v_size_658_);
v___x_666_ = lean_nat_dec_lt(v_size_659_, v___x_665_);
lean_dec(v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_695_; 
lean_inc(v_r_663_);
lean_inc(v_l_662_);
lean_inc(v_v_661_);
lean_inc(v_k_660_);
v_isSharedCheck_695_ = !lean_is_exclusive(v_r_646_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; 
v_unused_696_ = lean_ctor_get(v_r_646_, 4);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_r_646_, 3);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_r_646_, 2);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_r_646_, 1);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_r_646_, 0);
lean_dec(v_unused_700_);
v___x_668_ = v_r_646_;
v_isShared_669_ = v_isSharedCheck_695_;
goto v_resetjp_667_;
}
else
{
lean_dec(v_r_646_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_695_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___x_683_; lean_object* v___y_685_; 
v___x_670_ = lean_nat_add(v___x_640_, v_size_642_);
lean_dec(v_size_642_);
v___x_671_ = lean_nat_add(v___x_670_, v_size_641_);
lean_dec(v___x_670_);
v___x_683_ = lean_nat_add(v___x_640_, v_size_658_);
if (lean_obj_tag(v_l_662_) == 0)
{
lean_object* v_size_693_; 
v_size_693_ = lean_ctor_get(v_l_662_, 0);
lean_inc(v_size_693_);
v___y_685_ = v_size_693_;
goto v___jp_684_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v___y_685_ = v___x_694_;
goto v___jp_684_;
}
v___jp_672_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_nat_add(v___y_673_, v___y_675_);
lean_dec(v___y_675_);
lean_dec(v___y_673_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 4, v_impl_639_);
lean_ctor_set(v___x_668_, 3, v_r_663_);
lean_ctor_set(v___x_668_, 2, v_v_147_);
lean_ctor_set(v___x_668_, 1, v_k_146_);
lean_ctor_set(v___x_668_, 0, v___x_676_);
v___x_678_ = v___x_668_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_682_, 3, v_r_663_);
lean_ctor_set(v_reuseFailAlloc_682_, 4, v_impl_639_);
v___x_678_ = v_reuseFailAlloc_682_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_680_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v___x_678_);
lean_ctor_set(v___x_656_, 3, v___y_674_);
lean_ctor_set(v___x_656_, 2, v_v_661_);
lean_ctor_set(v___x_656_, 1, v_k_660_);
lean_ctor_set(v___x_656_, 0, v___x_671_);
v___x_680_ = v___x_656_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_k_660_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_v_661_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v___y_674_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = lean_nat_add(v___x_683_, v___y_685_);
lean_dec(v___y_685_);
lean_dec(v___x_683_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v_l_662_);
lean_ctor_set(v___x_151_, 3, v_l_645_);
lean_ctor_set(v___x_151_, 2, v_v_644_);
lean_ctor_set(v___x_151_, 1, v_k_643_);
lean_ctor_set(v___x_151_, 0, v___x_686_);
v___x_688_ = v___x_151_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_692_, 3, v_l_645_);
lean_ctor_set(v_reuseFailAlloc_692_, 4, v_l_662_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; 
v___x_689_ = lean_nat_add(v___x_640_, v_size_641_);
if (lean_obj_tag(v_r_663_) == 0)
{
lean_object* v_size_690_; 
v_size_690_ = lean_ctor_get(v_r_663_, 0);
lean_inc(v_size_690_);
v___y_673_ = v___x_689_;
v___y_674_ = v___x_688_;
v___y_675_ = v_size_690_;
goto v___jp_672_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___y_673_ = v___x_689_;
v___y_674_ = v___x_688_;
v___y_675_ = v___x_691_;
goto v___jp_672_;
}
}
}
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
lean_del_object(v___x_151_);
v___x_701_ = lean_nat_add(v___x_640_, v_size_642_);
lean_dec(v_size_642_);
v___x_702_ = lean_nat_add(v___x_701_, v_size_641_);
lean_dec(v___x_701_);
v___x_703_ = lean_nat_add(v___x_640_, v_size_641_);
v___x_704_ = lean_nat_add(v___x_703_, v_size_659_);
lean_dec(v___x_703_);
lean_inc_ref(v_impl_639_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 4, v_impl_639_);
lean_ctor_set(v___x_656_, 3, v_r_646_);
lean_ctor_set(v___x_656_, 2, v_v_147_);
lean_ctor_set(v___x_656_, 1, v_k_146_);
lean_ctor_set(v___x_656_, 0, v___x_704_);
v___x_706_ = v___x_656_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v_r_646_);
lean_ctor_set(v_reuseFailAlloc_719_, 4, v_impl_639_);
v___x_706_ = v_reuseFailAlloc_719_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_isSharedCheck_713_ = !lean_is_exclusive(v_impl_639_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; lean_object* v_unused_716_; lean_object* v_unused_717_; lean_object* v_unused_718_; 
v_unused_714_ = lean_ctor_get(v_impl_639_, 4);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_impl_639_, 3);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_impl_639_, 2);
lean_dec(v_unused_716_);
v_unused_717_ = lean_ctor_get(v_impl_639_, 1);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_impl_639_, 0);
lean_dec(v_unused_718_);
v___x_708_ = v_impl_639_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_dec(v_impl_639_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 4, v___x_706_);
lean_ctor_set(v___x_708_, 3, v_l_645_);
lean_ctor_set(v___x_708_, 2, v_v_644_);
lean_ctor_set(v___x_708_, 1, v_k_643_);
lean_ctor_set(v___x_708_, 0, v___x_702_);
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_k_643_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_v_644_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_l_645_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v___x_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v_size_726_ = lean_ctor_get(v_impl_639_, 0);
v___x_727_ = lean_nat_add(v___x_640_, v_size_726_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v_impl_639_);
lean_ctor_set(v___x_151_, 0, v___x_727_);
v___x_729_ = v___x_151_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_l_148_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_impl_639_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
else
{
if (lean_obj_tag(v_l_148_) == 0)
{
lean_object* v_l_731_; 
v_l_731_ = lean_ctor_get(v_l_148_, 3);
if (lean_obj_tag(v_l_731_) == 0)
{
lean_object* v_r_732_; 
lean_inc_ref(v_l_731_);
v_r_732_ = lean_ctor_get(v_l_148_, 4);
lean_inc(v_r_732_);
if (lean_obj_tag(v_r_732_) == 0)
{
lean_object* v_size_733_; lean_object* v_k_734_; lean_object* v_v_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_748_; 
v_size_733_ = lean_ctor_get(v_l_148_, 0);
v_k_734_ = lean_ctor_get(v_l_148_, 1);
v_v_735_ = lean_ctor_get(v_l_148_, 2);
v_isSharedCheck_748_ = !lean_is_exclusive(v_l_148_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; lean_object* v_unused_750_; 
v_unused_749_ = lean_ctor_get(v_l_148_, 4);
lean_dec(v_unused_749_);
v_unused_750_ = lean_ctor_get(v_l_148_, 3);
lean_dec(v_unused_750_);
v___x_737_ = v_l_148_;
v_isShared_738_ = v_isSharedCheck_748_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_v_735_);
lean_inc(v_k_734_);
lean_inc(v_size_733_);
lean_dec(v_l_148_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_748_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_size_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
v_size_739_ = lean_ctor_get(v_r_732_, 0);
v___x_740_ = lean_nat_add(v___x_640_, v_size_733_);
lean_dec(v_size_733_);
v___x_741_ = lean_nat_add(v___x_640_, v_size_739_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 4, v_impl_639_);
lean_ctor_set(v___x_737_, 3, v_r_732_);
lean_ctor_set(v___x_737_, 2, v_v_147_);
lean_ctor_set(v___x_737_, 1, v_k_146_);
lean_ctor_set(v___x_737_, 0, v___x_741_);
v___x_743_ = v___x_737_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v_r_732_);
lean_ctor_set(v_reuseFailAlloc_747_, 4, v_impl_639_);
v___x_743_ = v_reuseFailAlloc_747_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v___x_743_);
lean_ctor_set(v___x_151_, 3, v_l_731_);
lean_ctor_set(v___x_151_, 2, v_v_735_);
lean_ctor_set(v___x_151_, 1, v_k_734_);
lean_ctor_set(v___x_151_, 0, v___x_740_);
v___x_745_ = v___x_151_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_k_734_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_v_735_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_l_731_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_k_751_; lean_object* v_v_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_763_; 
v_k_751_ = lean_ctor_get(v_l_148_, 1);
v_v_752_ = lean_ctor_get(v_l_148_, 2);
v_isSharedCheck_763_ = !lean_is_exclusive(v_l_148_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; lean_object* v_unused_765_; lean_object* v_unused_766_; 
v_unused_764_ = lean_ctor_get(v_l_148_, 4);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_l_148_, 3);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_l_148_, 0);
lean_dec(v_unused_766_);
v___x_754_ = v_l_148_;
v_isShared_755_ = v_isSharedCheck_763_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_v_752_);
lean_inc(v_k_751_);
lean_dec(v_l_148_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_763_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_756_ = lean_unsigned_to_nat(3u);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 3, v_r_732_);
lean_ctor_set(v___x_754_, 2, v_v_147_);
lean_ctor_set(v___x_754_, 1, v_k_146_);
lean_ctor_set(v___x_754_, 0, v___x_640_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_r_732_);
lean_ctor_set(v_reuseFailAlloc_762_, 4, v_r_732_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v___x_758_);
lean_ctor_set(v___x_151_, 3, v_l_731_);
lean_ctor_set(v___x_151_, 2, v_v_752_);
lean_ctor_set(v___x_151_, 1, v_k_751_);
lean_ctor_set(v___x_151_, 0, v___x_756_);
v___x_760_ = v___x_151_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_k_751_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_v_752_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_l_731_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
else
{
lean_object* v_r_767_; 
v_r_767_ = lean_ctor_get(v_l_148_, 4);
lean_inc(v_r_767_);
if (lean_obj_tag(v_r_767_) == 0)
{
lean_object* v_k_768_; lean_object* v_v_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_792_; 
lean_inc(v_l_731_);
v_k_768_ = lean_ctor_get(v_l_148_, 1);
v_v_769_ = lean_ctor_get(v_l_148_, 2);
v_isSharedCheck_792_ = !lean_is_exclusive(v_l_148_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; 
v_unused_793_ = lean_ctor_get(v_l_148_, 4);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_l_148_, 3);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_l_148_, 0);
lean_dec(v_unused_795_);
v___x_771_ = v_l_148_;
v_isShared_772_ = v_isSharedCheck_792_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_v_769_);
lean_inc(v_k_768_);
lean_dec(v_l_148_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_792_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_k_773_; lean_object* v_v_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_788_; 
v_k_773_ = lean_ctor_get(v_r_767_, 1);
v_v_774_ = lean_ctor_get(v_r_767_, 2);
v_isSharedCheck_788_ = !lean_is_exclusive(v_r_767_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; 
v_unused_789_ = lean_ctor_get(v_r_767_, 4);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_r_767_, 3);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_r_767_, 0);
lean_dec(v_unused_791_);
v___x_776_ = v_r_767_;
v_isShared_777_ = v_isSharedCheck_788_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_v_774_);
lean_inc(v_k_773_);
lean_dec(v_r_767_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_788_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_unsigned_to_nat(3u);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 4, v_l_731_);
lean_ctor_set(v___x_776_, 3, v_l_731_);
lean_ctor_set(v___x_776_, 2, v_v_769_);
lean_ctor_set(v___x_776_, 1, v_k_768_);
lean_ctor_set(v___x_776_, 0, v___x_640_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_k_768_);
lean_ctor_set(v_reuseFailAlloc_787_, 2, v_v_769_);
lean_ctor_set(v_reuseFailAlloc_787_, 3, v_l_731_);
lean_ctor_set(v_reuseFailAlloc_787_, 4, v_l_731_);
v___x_780_ = v_reuseFailAlloc_787_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 4, v_l_731_);
lean_ctor_set(v___x_771_, 2, v_v_147_);
lean_ctor_set(v___x_771_, 1, v_k_146_);
lean_ctor_set(v___x_771_, 0, v___x_640_);
v___x_782_ = v___x_771_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_l_731_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_l_731_);
v___x_782_ = v_reuseFailAlloc_786_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v___x_782_);
lean_ctor_set(v___x_151_, 3, v___x_780_);
lean_ctor_set(v___x_151_, 2, v_v_774_);
lean_ctor_set(v___x_151_, 1, v_k_773_);
lean_ctor_set(v___x_151_, 0, v___x_778_);
v___x_784_ = v___x_151_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_k_773_);
lean_ctor_set(v_reuseFailAlloc_785_, 2, v_v_774_);
lean_ctor_set(v_reuseFailAlloc_785_, 3, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_785_, 4, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_unsigned_to_nat(2u);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v_r_767_);
lean_ctor_set(v___x_151_, 0, v___x_796_);
v___x_798_ = v___x_151_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_l_148_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v_r_767_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
lean_object* v___x_801_; 
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 4, v_l_148_);
lean_ctor_set(v___x_151_, 0, v___x_640_);
v___x_801_ = v___x_151_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_k_146_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_v_147_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_l_148_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v_l_148_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
}
else
{
return v_t_145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___redArg___boxed(lean_object* v_k_805_, lean_object* v_t_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___redArg(v_k_805_, v_t_806_);
lean_dec(v_k_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement(lean_object* v_m_808_, lean_object* v_x_809_){
_start:
{
lean_object* v_snd_810_; 
v_snd_810_ = lean_ctor_get(v_x_809_, 1);
if (lean_obj_tag(v_snd_810_) == 0)
{
lean_object* v_fst_811_; lean_object* v___x_812_; 
v_fst_811_ = lean_ctor_get(v_x_809_, 0);
lean_inc(v_fst_811_);
lean_dec_ref(v_x_809_);
v___x_812_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___redArg(v_fst_811_, v_m_808_);
lean_dec(v_fst_811_);
return v___x_812_;
}
else
{
lean_object* v_fst_813_; lean_object* v_val_814_; lean_object* v___x_815_; 
lean_inc_ref(v_snd_810_);
v_fst_813_ = lean_ctor_get(v_x_809_, 0);
lean_inc(v_fst_813_);
lean_dec_ref(v_x_809_);
v_val_814_ = lean_ctor_get(v_snd_810_, 0);
lean_inc(v_val_814_);
lean_dec_ref_known(v_snd_810_, 1);
v___x_815_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_813_, v_val_814_, v_m_808_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0(lean_object* v_00_u03b2_816_, lean_object* v_k_817_, lean_object* v_t_818_, lean_object* v_h_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___redArg(v_k_817_, v_t_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0___boxed(lean_object* v_00_u03b2_821_, lean_object* v_k_822_, lean_object* v_t_823_, lean_object* v_h_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement_spec__0(v_00_u03b2_821_, v_k_822_, v_t_823_, v_h_824_);
lean_dec(v_k_822_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_(lean_object* v_es_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = lean_array_mk(v_es_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_828_, size_t v_i_829_, size_t v_stop_830_, lean_object* v_b_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = lean_usize_dec_eq(v_i_829_, v_stop_830_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; size_t v___x_835_; size_t v___x_836_; 
v___x_833_ = lean_array_uget_borrowed(v_as_828_, v_i_829_);
lean_inc(v___x_833_);
v___x_834_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_insertReplacement(v_b_831_, v___x_833_);
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_add(v_i_829_, v___x_835_);
v_i_829_ = v___x_836_;
v_b_831_ = v___x_834_;
goto _start;
}
else
{
return v_b_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_838_, lean_object* v_i_839_, lean_object* v_stop_840_, lean_object* v_b_841_){
_start:
{
size_t v_i_boxed_842_; size_t v_stop_boxed_843_; lean_object* v_res_844_; 
v_i_boxed_842_ = lean_unbox_usize(v_i_839_);
lean_dec(v_i_839_);
v_stop_boxed_843_ = lean_unbox_usize(v_stop_840_);
lean_dec(v_stop_840_);
v_res_844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__0(v_as_838_, v_i_boxed_842_, v_stop_boxed_843_, v_b_841_);
lean_dec_ref(v_as_838_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_845_, size_t v_i_846_, size_t v_stop_847_, lean_object* v_b_848_){
_start:
{
lean_object* v___y_850_; uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_eq(v_i_846_, v_stop_847_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_855_ = lean_array_uget_borrowed(v_as_845_, v_i_846_);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_array_get_size(v___x_855_);
v___x_858_ = lean_nat_dec_lt(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
v___y_850_ = v_b_848_;
goto v___jp_849_;
}
else
{
size_t v___x_859_; size_t v___x_860_; lean_object* v___x_861_; 
v___x_859_ = ((size_t)0ULL);
v___x_860_ = lean_usize_of_nat(v___x_857_);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__0(v___x_855_, v___x_859_, v___x_860_, v_b_848_);
v___y_850_ = v___x_861_;
goto v___jp_849_;
}
}
else
{
return v_b_848_;
}
v___jp_849_:
{
size_t v___x_851_; size_t v___x_852_; 
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_846_, v___x_851_);
v_i_846_ = v___x_852_;
v_b_848_ = v___y_850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_862_, lean_object* v_i_863_, lean_object* v_stop_864_, lean_object* v_b_865_){
_start:
{
size_t v_i_boxed_866_; size_t v_stop_boxed_867_; lean_object* v_res_868_; 
v_i_boxed_866_ = lean_unbox_usize(v_i_863_);
lean_dec(v_i_863_);
v_stop_boxed_867_ = lean_unbox_usize(v_stop_864_);
lean_dec(v_stop_864_);
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__1(v_as_862_, v_i_boxed_866_, v_stop_boxed_867_, v_b_865_);
lean_dec_ref(v_as_862_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0(lean_object* v_initState_869_, lean_object* v_as_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_array_get_size(v_as_870_);
v___x_873_ = lean_nat_dec_lt(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
return v_initState_869_;
}
else
{
size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_874_ = ((size_t)0ULL);
v___x_875_ = lean_usize_of_nat(v___x_872_);
v___x_876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0_spec__1(v_as_870_, v___x_874_, v___x_875_, v_initState_869_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_877_, lean_object* v_as_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2__spec__0(v_initState_877_, v_as_878_);
lean_dec_ref(v_as_878_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_));
v___x_899_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2____boxed(lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_();
return v_res_901_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isDeprecatedSyntax(lean_object* v_env_902_, lean_object* v_kind_903_){
_start:
{
lean_object* v___x_904_; lean_object* v_toEnvExtension_905_; lean_object* v_asyncMode_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_904_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_905_ = lean_ctor_get(v___x_904_, 0);
v_asyncMode_906_ = lean_ctor_get(v_toEnvExtension_905_, 2);
v___x_907_ = lean_box(1);
v___x_908_ = lean_box(0);
v___x_909_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_907_, v___x_904_, v_env_902_, v_asyncMode_906_, v___x_908_);
v___x_910_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_kind_903_, v___x_909_);
lean_dec(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isDeprecatedSyntax___boxed(lean_object* v_env_911_, lean_object* v_kind_912_){
_start:
{
uint8_t v_res_913_; lean_object* v_r_914_; 
v_res_913_ = l_Lean_Elab_isDeprecatedSyntax(v_env_911_, v_kind_912_);
lean_dec(v_kind_912_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_915_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_919_ = lean_unsigned_to_nat(0u);
v___x_920_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
lean_ctor_set(v___x_920_, 2, v___x_919_);
lean_ctor_set(v___x_920_, 3, v___x_919_);
lean_ctor_set(v___x_920_, 4, v___x_918_);
lean_ctor_set(v___x_920_, 5, v___x_918_);
lean_ctor_set(v___x_920_, 6, v___x_918_);
lean_ctor_set(v___x_920_, 7, v___x_918_);
lean_ctor_set(v___x_920_, 8, v___x_918_);
lean_ctor_set(v___x_920_, 9, v___x_918_);
lean_ctor_set(v___x_920_, 10, v___x_918_);
return v___x_920_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_unsigned_to_nat(32u);
v___x_922_ = lean_mk_empty_array_with_capacity(v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_924_ = ((size_t)5ULL);
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_unsigned_to_nat(32u);
v___x_927_ = lean_mk_empty_array_with_capacity(v___x_926_);
v___x_928_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_929_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_927_);
lean_ctor_set(v___x_929_, 2, v___x_925_);
lean_ctor_set(v___x_929_, 3, v___x_925_);
lean_ctor_set_usize(v___x_929_, 4, v___x_924_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_930_ = lean_box(1);
v___x_931_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_931_);
lean_ctor_set(v___x_933_, 2, v___x_930_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; lean_object* v_toCold_939_; lean_object* v_env_940_; lean_object* v_options_941_; uint8_t v___x_942_; lean_object* v_env_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_938_ = lean_st_ref_get(v___y_936_);
v_toCold_939_ = lean_ctor_get(v___y_935_, 0);
v_env_940_ = lean_ctor_get(v___x_938_, 0);
lean_inc_ref(v_env_940_);
lean_dec(v___x_938_);
v_options_941_ = lean_ctor_get(v_toCold_939_, 2);
v___x_942_ = 0;
v_env_943_ = l_Lean_Environment_setRecordingDeps(v_env_940_, v___x_942_);
v___x_944_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_945_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_941_);
v___x_946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_946_, 0, v_env_943_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
lean_ctor_set(v___x_946_, 3, v_options_941_);
v___x_947_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_msgData_934_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_ref_958_; lean_object* v___x_959_; lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_968_; 
v_ref_958_ = lean_ctor_get(v___y_955_, 2);
v___x_959_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_954_, v___y_955_, v___y_956_);
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_968_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_968_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
lean_inc(v_ref_958_);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v_ref_958_);
lean_ctor_set(v___x_964_, 1, v_a_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set_tag(v___x_962_, 1);
lean_ctor_set(v___x_962_, 0, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(lean_object* v_x_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
if (lean_obj_tag(v_x_974_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_a_978_ = lean_ctor_get(v_x_974_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v_x_974_, 1);
v___x_979_ = l_Lean_stringToMessageData(v_a_978_);
v___x_980_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(v___x_979_, v___y_975_, v___y_976_);
return v___x_980_;
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_a_981_ = lean_ctor_get(v_x_974_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v_x_974_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v_x_974_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v_x_974_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 0);
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(v_x_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_993_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_box(0);
v___x_995_ = l_Lean_Elab_abortCommandExceptionId;
v___x_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg();
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg(lean_object* v_typeName_1002_, lean_object* v_constName_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v_env_1008_; uint8_t v___x_1009_; 
v___x_1007_ = lean_st_ref_get(v___y_1005_);
v_env_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc_ref(v_env_1008_);
lean_dec(v___x_1007_);
lean_inc(v_constName_1003_);
v___x_1009_ = lean_has_compile_error(v_env_1008_, v_constName_1003_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; lean_object* v_env_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1010_ = lean_st_ref_get(v___y_1005_);
v_env_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc_ref(v_env_1011_);
lean_dec(v___x_1010_);
v___x_1012_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1004_);
v___x_1013_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1011_, v___x_1012_, v_typeName_1002_, v_constName_1003_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(v___x_1013_, v___y_1004_, v___y_1005_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v___x_1016_; lean_object* v_env_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec_ref_known(v___x_1015_, 1);
v___x_1016_ = lean_st_ref_get(v___y_1005_);
v_env_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc_ref(v_env_1017_);
lean_dec(v___x_1016_);
v___x_1018_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1004_);
v___x_1019_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1017_, v___x_1018_, v_typeName_1002_, v_constName_1003_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(v___x_1019_, v___y_1004_, v___y_1005_);
return v___x_1020_;
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v_constName_1003_);
lean_dec(v_typeName_1002_);
v_a_1021_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1015_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1015_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg___boxed(lean_object* v_typeName_1029_, lean_object* v_constName_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg(v_typeName_1029_, v_constName_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe(lean_object* v_declName_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__1));
v___x_1044_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg(v___x_1043_, v_declName_1039_, v_a_1040_, v_a_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___boxed(lean_object* v_declName_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe(v_declName_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg();
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1(v_00_u03b1_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0(lean_object* v_00_u03b1_1060_, lean_object* v_typeName_1061_, lean_object* v_constName_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg(v_typeName_1061_, v_constName_1062_, v___y_1063_, v___y_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_typeName_1068_, lean_object* v_constName_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0(v_00_u03b1_1067_, v_typeName_1068_, v_constName_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_1074_, lean_object* v_x_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(v_x_1075_, v___y_1076_, v___y_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0(v_00_u03b1_1080_, v_x_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1086_, lean_object* v_msg_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_1087_, v___y_1088_, v___y_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_msg_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_1092_, v_msg_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0(uint8_t v___x_1098_, lean_object* v_s_1099_){
_start:
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Lean_Syntax_isAtom(v_s_1099_);
if (v___x_1103_ == 0)
{
uint8_t v___x_1104_; 
v___x_1104_ = l_Lean_Syntax_isIdent(v_s_1099_);
if (v___x_1104_ == 0)
{
return v___x_1104_;
}
else
{
goto v___jp_1100_;
}
}
else
{
goto v___jp_1100_;
}
v___jp_1100_:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_Syntax_getHeadInfo(v_s_1099_);
if (lean_obj_tag(v___x_1101_) == 0)
{
uint8_t v___x_1102_; 
lean_dec_ref_known(v___x_1101_, 4);
v___x_1102_ = 0;
return v___x_1102_;
}
else
{
lean_dec(v___x_1101_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0___boxed(lean_object* v___x_1105_, lean_object* v_s_1106_){
_start:
{
uint8_t v___x_10040__boxed_1107_; uint8_t v_res_1108_; lean_object* v_r_1109_; 
v___x_10040__boxed_1107_ = lean_unbox(v___x_1105_);
v_res_1108_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0(v___x_10040__boxed_1107_, v_s_1106_);
lean_dec(v_s_1106_);
v_r_1109_ = lean_box(v_res_1108_);
return v_r_1109_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_box(0);
v___x_1111_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v___x_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg(){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___closed__0);
v___x_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___boxed(lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg();
return v_res_1117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(lean_object* v_env_1118_, lean_object* v_nm_1119_){
_start:
{
uint8_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = 1;
v___x_1121_ = l_Lean_Environment_contains(v_env_1118_, v_nm_1119_, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0___boxed(lean_object* v_env_1122_, lean_object* v_nm_1123_){
_start:
{
uint8_t v_res_1124_; lean_object* v_r_1125_; 
v_res_1124_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(v_env_1122_, v_nm_1123_);
v_r_1125_ = lean_box(v_res_1124_);
return v_r_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1(lean_object* v_env_1126_, lean_object* v_declName_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v___x_1130_; lean_object* v_env_1131_; uint8_t v___x_1132_; 
v___x_1130_ = 0;
v_env_1131_ = l_Lean_Environment_setExporting(v_env_1126_, v___x_1130_);
lean_inc(v_declName_1127_);
lean_inc_ref(v_env_1131_);
v___x_1132_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(v_env_1131_, v_declName_1127_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
lean_inc(v_declName_1127_);
v___x_1133_ = l_Lean_mkPrivateName(v_env_1131_, v_declName_1127_);
lean_inc_ref(v_env_1131_);
v___x_1134_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(v_env_1131_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_privateToUserName_x3f(v_declName_1127_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec_ref(v_env_1131_);
v___x_1136_ = lean_box(v___x_1134_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___y_1129_);
return v___x_1137_;
}
else
{
lean_object* v_val_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_val_1138_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_val_1138_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1139_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(v_env_1131_, v_val_1138_);
v___x_1140_ = lean_box(v___x_1139_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___y_1129_);
return v___x_1141_;
}
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_dec_ref(v_env_1131_);
lean_dec(v_declName_1127_);
v___x_1142_ = lean_box(v___x_1134_);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v___y_1129_);
return v___x_1143_;
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec_ref(v_env_1131_);
lean_dec(v_declName_1127_);
v___x_1144_ = lean_box(v___x_1132_);
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v___y_1129_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1___boxed(lean_object* v_env_1146_, lean_object* v_declName_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1(v_env_1146_, v_declName_1147_, v___y_1148_, v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(lean_object* v_ref_1151_, lean_object* v_msg_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_toCold_1156_; lean_object* v_currRecDepth_1157_; lean_object* v_ref_1158_; uint16_t v_optionFlags_1159_; uint8_t v_suppressElabErrors_1160_; uint8_t v_checkDeprecated_1161_; uint8_t v_isRecordingDeps_1162_; lean_object* v_ref_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_toCold_1156_ = lean_ctor_get(v___y_1153_, 0);
v_currRecDepth_1157_ = lean_ctor_get(v___y_1153_, 1);
v_ref_1158_ = lean_ctor_get(v___y_1153_, 2);
v_optionFlags_1159_ = lean_ctor_get_uint16(v___y_1153_, sizeof(void*)*3);
v_suppressElabErrors_1160_ = lean_ctor_get_uint8(v___y_1153_, sizeof(void*)*3 + 2);
v_checkDeprecated_1161_ = lean_ctor_get_uint8(v___y_1153_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1162_ = lean_ctor_get_uint8(v___y_1153_, sizeof(void*)*3 + 4);
v_ref_1163_ = l_Lean_replaceRef(v_ref_1151_, v_ref_1158_);
lean_inc(v_currRecDepth_1157_);
lean_inc_ref(v_toCold_1156_);
v___x_1164_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1164_, 0, v_toCold_1156_);
lean_ctor_set(v___x_1164_, 1, v_currRecDepth_1157_);
lean_ctor_set(v___x_1164_, 2, v_ref_1163_);
lean_ctor_set_uint16(v___x_1164_, sizeof(void*)*3, v_optionFlags_1159_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*3 + 2, v_suppressElabErrors_1160_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*3 + 3, v_checkDeprecated_1161_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*3 + 4, v_isRecordingDeps_1162_);
v___x_1165_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_1152_, v___x_1164_, v___y_1154_);
lean_dec_ref_known(v___x_1164_, 3);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1166_, lean_object* v_msg_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(v_ref_1166_, v_msg_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v_ref_1166_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__5(lean_object* v_env_1172_, lean_object* v_currNamespace_1173_, lean_object* v_openDecls_1174_, lean_object* v_n_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = l_Lean_ResolveName_resolveNamespace(v_env_1172_, v_currNamespace_1173_, v_openDecls_1174_, v_n_1175_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v___y_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__5___boxed(lean_object* v_env_1180_, lean_object* v_currNamespace_1181_, lean_object* v_openDecls_1182_, lean_object* v_n_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__5(v_env_1180_, v_currNamespace_1181_, v_openDecls_1182_, v_n_1183_, v___y_1184_, v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4(lean_object* v_env_1187_, lean_object* v___x_1188_, lean_object* v_currNamespace_1189_, lean_object* v_openDecls_1190_, lean_object* v_n_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = l_Lean_ResolveName_resolveGlobalName(v_env_1187_, v___x_1188_, v_currNamespace_1189_, v_openDecls_1190_, v_n_1191_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v___y_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4___boxed(lean_object* v_env_1196_, lean_object* v___x_1197_, lean_object* v_currNamespace_1198_, lean_object* v_openDecls_1199_, lean_object* v_n_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4(v_env_1196_, v___x_1197_, v_currNamespace_1198_, v_openDecls_1199_, v_n_1200_, v___y_1201_, v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec_ref(v___x_1197_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3(lean_object* v_currNamespace_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_currNamespace_1204_);
lean_ctor_set(v___x_1207_, 1, v___y_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3___boxed(lean_object* v_currNamespace_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3(v_currNamespace_1208_, v___y_1209_, v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(lean_object* v_x_1212_, lean_object* v___y_1213_){
_start:
{
if (lean_obj_tag(v_x_1212_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1215_; 
v_a_1214_ = lean_ctor_get(v_x_1212_, 0);
lean_inc(v_a_1214_);
v___x_1215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_a_1214_);
lean_ctor_set(v___x_1215_, 1, v___y_1213_);
return v___x_1215_;
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1216_ = lean_ctor_get(v_x_1212_, 0);
lean_inc(v_a_1216_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_a_1216_);
lean_ctor_set(v___x_1217_, 1, v___y_1213_);
return v___x_1217_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg___boxed(lean_object* v_x_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(v_x_1218_, v___y_1219_);
lean_dec_ref(v_x_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2(lean_object* v_env_1221_, lean_object* v_stx_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1221_, v_stx_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
if (lean_obj_tag(v_a_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
v_a_1227_ = lean_ctor_get(v___x_1225_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1225_, 0);
lean_dec(v_unused_1236_);
v___x_1229_ = v___x_1225_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1225_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = lean_box(0);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_a_1227_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v_val_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1265_; 
v_val_1237_ = lean_ctor_get(v_a_1226_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_a_1226_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1239_ = v_a_1226_;
v_isShared_1240_ = v_isSharedCheck_1265_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_val_1237_);
lean_dec(v_a_1226_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1265_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_snd_1241_; 
v_snd_1241_ = lean_ctor_get(v_val_1237_, 1);
lean_inc(v_snd_1241_);
lean_dec(v_val_1237_);
if (lean_obj_tag(v_snd_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1251_; 
lean_del_object(v___x_1239_);
v_a_1242_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1225_, 2);
v_a_1243_ = lean_ctor_get(v_snd_1241_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_snd_1241_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1245_ = v_snd_1241_;
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v_snd_1241_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(v___x_1248_, v_a_1242_);
lean_dec_ref(v___x_1248_);
return v___x_1249_;
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1264_; 
v_a_1252_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1225_, 2);
v_a_1253_ = lean_ctor_get(v_snd_1241_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_snd_1241_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1255_ = v_snd_1241_;
v_isShared_1256_ = v_isSharedCheck_1264_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v_snd_1241_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1264_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v_a_1253_);
v___x_1258_ = v___x_1239_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
lean_object* v___x_1260_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1258_);
v___x_1260_ = v___x_1255_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(v___x_1260_, v_a_1252_);
lean_dec_ref(v___x_1260_);
return v___x_1261_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_a_1266_ = lean_ctor_get(v___x_1225_, 0);
v_a_1267_ = lean_ctor_get(v___x_1225_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1225_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_inc(v_a_1266_);
lean_dec(v___x_1225_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1266_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2___boxed(lean_object* v_env_1275_, lean_object* v_stx_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2(v_env_1275_, v_stx_1276_, v___y_1277_, v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1279_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = l_Lean_maxRecDepthErrorMessage;
v___x_1286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3);
v___x_1288_ = l_Lean_MessageData_ofFormat(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4);
v___x_1290_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__2));
v___x_1291_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(lean_object* v_ref_1292_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_ref_1292_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(v_ref_1297_);
return v_res_1299_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1300_; double v___x_1301_; 
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_float_of_nat(v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(lean_object* v_cls_1305_, lean_object* v_msg_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_ref_1310_; lean_object* v___x_1311_; lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1357_; 
v_ref_1310_ = lean_ctor_get(v___y_1307_, 2);
v___x_1311_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_1306_, v___y_1307_, v___y_1308_);
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1357_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1357_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v_traceState_1317_; lean_object* v_env_1318_; lean_object* v_nextMacroScope_1319_; lean_object* v_ngen_1320_; lean_object* v_auxDeclNGen_1321_; lean_object* v_cache_1322_; lean_object* v_recordedDeps_1323_; lean_object* v_messages_1324_; lean_object* v_infoState_1325_; lean_object* v_snapshotTasks_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1356_; 
v___x_1316_ = lean_st_ref_take(v___y_1308_);
v_traceState_1317_ = lean_ctor_get(v___x_1316_, 4);
v_env_1318_ = lean_ctor_get(v___x_1316_, 0);
v_nextMacroScope_1319_ = lean_ctor_get(v___x_1316_, 1);
v_ngen_1320_ = lean_ctor_get(v___x_1316_, 2);
v_auxDeclNGen_1321_ = lean_ctor_get(v___x_1316_, 3);
v_cache_1322_ = lean_ctor_get(v___x_1316_, 5);
v_recordedDeps_1323_ = lean_ctor_get(v___x_1316_, 6);
v_messages_1324_ = lean_ctor_get(v___x_1316_, 7);
v_infoState_1325_ = lean_ctor_get(v___x_1316_, 8);
v_snapshotTasks_1326_ = lean_ctor_get(v___x_1316_, 9);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1328_ = v___x_1316_;
v_isShared_1329_ = v_isSharedCheck_1356_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_snapshotTasks_1326_);
lean_inc(v_infoState_1325_);
lean_inc(v_messages_1324_);
lean_inc(v_recordedDeps_1323_);
lean_inc(v_cache_1322_);
lean_inc(v_traceState_1317_);
lean_inc(v_auxDeclNGen_1321_);
lean_inc(v_ngen_1320_);
lean_inc(v_nextMacroScope_1319_);
lean_inc(v_env_1318_);
lean_dec(v___x_1316_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1356_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
uint64_t v_tid_1330_; lean_object* v_traces_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1355_; 
v_tid_1330_ = lean_ctor_get_uint64(v_traceState_1317_, sizeof(void*)*1);
v_traces_1331_ = lean_ctor_get(v_traceState_1317_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_traceState_1317_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1333_ = v_traceState_1317_;
v_isShared_1334_ = v_isSharedCheck_1355_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_traces_1331_);
lean_dec(v_traceState_1317_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1355_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; double v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1335_ = lean_box(0);
v___x_1336_ = lean_box(0);
v___x_1337_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0);
v___x_1338_ = 0;
v___x_1339_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1));
v___x_1340_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1340_, 0, v_cls_1305_);
lean_ctor_set(v___x_1340_, 1, v___x_1336_);
lean_ctor_set(v___x_1340_, 2, v___x_1339_);
lean_ctor_set_float(v___x_1340_, sizeof(void*)*3, v___x_1337_);
lean_ctor_set_float(v___x_1340_, sizeof(void*)*3 + 8, v___x_1337_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*3 + 16, v___x_1338_);
v___x_1341_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__2));
v___x_1342_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v_a_1312_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
lean_inc(v_ref_1310_);
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v_ref_1310_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = l_Lean_PersistentArray_push___redArg(v_traces_1331_, v___x_1343_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1344_);
v___x_1346_ = v___x_1333_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1344_);
lean_ctor_set_uint64(v_reuseFailAlloc_1354_, sizeof(void*)*1, v_tid_1330_);
v___x_1346_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1348_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 4, v___x_1346_);
v___x_1348_ = v___x_1328_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_env_1318_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_nextMacroScope_1319_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_ngen_1320_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v_auxDeclNGen_1321_);
lean_ctor_set(v_reuseFailAlloc_1353_, 4, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1353_, 5, v_cache_1322_);
lean_ctor_set(v_reuseFailAlloc_1353_, 6, v_recordedDeps_1323_);
lean_ctor_set(v_reuseFailAlloc_1353_, 7, v_messages_1324_);
lean_ctor_set(v_reuseFailAlloc_1353_, 8, v_infoState_1325_);
lean_ctor_set(v_reuseFailAlloc_1353_, 9, v_snapshotTasks_1326_);
v___x_1348_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_st_ref_put(v___y_1308_, v___x_1348_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1335_);
v___x_1351_ = v___x_1314_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1335_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___boxed(lean_object* v_cls_1358_, lean_object* v_msg_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(v_cls_1358_, v_msg_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4(lean_object* v_as_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
if (lean_obj_tag(v_as_1367_) == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
else
{
lean_object* v_toCold_1373_; lean_object* v_options_1374_; uint8_t v_hasTrace_1375_; 
v_toCold_1373_ = lean_ctor_get(v___y_1368_, 0);
v_options_1374_ = lean_ctor_get(v_toCold_1373_, 2);
v_hasTrace_1375_ = lean_ctor_get_uint8(v_options_1374_, sizeof(void*)*1);
if (v_hasTrace_1375_ == 0)
{
lean_object* v_tail_1376_; 
v_tail_1376_ = lean_ctor_get(v_as_1367_, 1);
lean_inc(v_tail_1376_);
lean_dec_ref_known(v_as_1367_, 2);
v_as_1367_ = v_tail_1376_;
goto _start;
}
else
{
lean_object* v_head_1378_; lean_object* v_tail_1379_; lean_object* v_fst_1380_; lean_object* v_snd_1381_; lean_object* v_inheritedTraceOptions_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_head_1378_ = lean_ctor_get(v_as_1367_, 0);
lean_inc(v_head_1378_);
v_tail_1379_ = lean_ctor_get(v_as_1367_, 1);
lean_inc(v_tail_1379_);
lean_dec_ref_known(v_as_1367_, 2);
v_fst_1380_ = lean_ctor_get(v_head_1378_, 0);
lean_inc_n(v_fst_1380_, 2);
v_snd_1381_ = lean_ctor_get(v_head_1378_, 1);
lean_inc(v_snd_1381_);
lean_dec(v_head_1378_);
v_inheritedTraceOptions_1382_ = lean_ctor_get(v_toCold_1373_, 11);
v___x_1383_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__1));
v___x_1384_ = l_Lean_Name_append(v___x_1383_, v_fst_1380_);
v___x_1385_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1382_, v_options_1374_, v___x_1384_);
lean_dec(v___x_1384_);
if (v___x_1385_ == 0)
{
lean_dec(v_snd_1381_);
lean_dec(v_fst_1380_);
v_as_1367_ = v_tail_1379_;
goto _start;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_snd_1381_);
v___x_1388_ = l_Lean_MessageData_ofFormat(v___x_1387_);
v___x_1389_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(v_fst_1380_, v___x_1388_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_dec_ref_known(v___x_1389_, 1);
v_as_1367_ = v_tail_1379_;
goto _start;
}
else
{
lean_dec(v_tail_1379_);
return v___x_1389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___boxed(lean_object* v_as_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4(v_as_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(lean_object* v_keys_1396_, lean_object* v_i_1397_, lean_object* v_k_1398_){
_start:
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = lean_array_get_size(v_keys_1396_);
v___x_1400_ = lean_nat_dec_lt(v_i_1397_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_dec(v_i_1397_);
return v___x_1400_;
}
else
{
lean_object* v_k_x27_1401_; uint8_t v___x_1402_; 
v_k_x27_1401_ = lean_array_fget_borrowed(v_keys_1396_, v_i_1397_);
v___x_1402_ = l_Lean_instBEqExtraModUse_beq(v_k_1398_, v_k_x27_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_unsigned_to_nat(1u);
v___x_1404_ = lean_nat_add(v_i_1397_, v___x_1403_);
lean_dec(v_i_1397_);
v_i_1397_ = v___x_1404_;
goto _start;
}
else
{
lean_dec(v_i_1397_);
return v___x_1400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg___boxed(lean_object* v_keys_1406_, lean_object* v_i_1407_, lean_object* v_k_1408_){
_start:
{
uint8_t v_res_1409_; lean_object* v_r_1410_; 
v_res_1409_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(v_keys_1406_, v_i_1407_, v_k_1408_);
lean_dec_ref(v_k_1408_);
lean_dec_ref(v_keys_1406_);
v_r_1410_ = lean_box(v_res_1409_);
return v_r_1410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1411_, size_t v_x_1412_, lean_object* v_x_1413_){
_start:
{
if (lean_obj_tag(v_x_1411_) == 0)
{
lean_object* v_es_1414_; lean_object* v___x_1415_; size_t v___x_1416_; size_t v___x_1417_; lean_object* v_j_1418_; lean_object* v___x_1419_; 
v_es_1414_ = lean_ctor_get(v_x_1411_, 0);
v___x_1415_ = lean_box(2);
v___x_1416_ = ((size_t)31ULL);
v___x_1417_ = lean_usize_land(v_x_1412_, v___x_1416_);
v_j_1418_ = lean_usize_to_nat(v___x_1417_);
v___x_1419_ = lean_array_get_borrowed(v___x_1415_, v_es_1414_, v_j_1418_);
lean_dec(v_j_1418_);
switch(lean_obj_tag(v___x_1419_))
{
case 0:
{
lean_object* v_key_1420_; uint8_t v___x_1421_; 
v_key_1420_ = lean_ctor_get(v___x_1419_, 0);
v___x_1421_ = l_Lean_instBEqExtraModUse_beq(v_x_1413_, v_key_1420_);
return v___x_1421_;
}
case 1:
{
lean_object* v_node_1422_; size_t v___x_1423_; size_t v___x_1424_; 
v_node_1422_ = lean_ctor_get(v___x_1419_, 0);
v___x_1423_ = ((size_t)5ULL);
v___x_1424_ = lean_usize_shift_right(v_x_1412_, v___x_1423_);
v_x_1411_ = v_node_1422_;
v_x_1412_ = v___x_1424_;
goto _start;
}
default: 
{
uint8_t v___x_1426_; 
v___x_1426_ = 0;
return v___x_1426_;
}
}
}
else
{
lean_object* v_ks_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v_ks_1427_ = lean_ctor_get(v_x_1411_, 0);
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(v_ks_1427_, v___x_1428_, v_x_1413_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_x_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_){
_start:
{
size_t v_x_10482__boxed_1433_; uint8_t v_res_1434_; lean_object* v_r_1435_; 
v_x_10482__boxed_1433_ = lean_unbox_usize(v_x_1431_);
lean_dec(v_x_1431_);
v_res_1434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(v_x_1430_, v_x_10482__boxed_1433_, v_x_1432_);
lean_dec_ref(v_x_1432_);
lean_dec_ref(v_x_1430_);
v_r_1435_ = lean_box(v_res_1434_);
return v_r_1435_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(lean_object* v_x_1436_, lean_object* v_x_1437_){
_start:
{
uint64_t v___x_1438_; size_t v___x_1439_; uint8_t v___x_1440_; 
v___x_1438_ = l_Lean_instHashableExtraModUse_hash(v_x_1437_);
v___x_1439_ = lean_uint64_to_usize(v___x_1438_);
v___x_1440_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(v_x_1436_, v___x_1439_, v_x_1437_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
uint8_t v_res_1443_; lean_object* v_r_1444_; 
v_res_1443_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(v_x_1441_, v_x_1442_);
lean_dec_ref(v_x_1442_);
lean_dec_ref(v_x_1441_);
v_r_1444_ = lean_box(v_res_1443_);
return v_r_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___lam__0(lean_object* v___x_1445_, lean_object* v_entry_1446_, lean_object* v_s_1447_){
_start:
{
lean_object* v_addEntryFn_1448_; lean_object* v_importedEntries_1449_; lean_object* v_state_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
v_addEntryFn_1448_ = lean_ctor_get(v___x_1445_, 3);
lean_inc(v_addEntryFn_1448_);
lean_dec_ref(v___x_1445_);
v_importedEntries_1449_ = lean_ctor_get(v_s_1447_, 0);
v_state_1450_ = lean_ctor_get(v_s_1447_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_s_1447_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1452_ = v_s_1447_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_state_1450_);
lean_inc(v_importedEntries_1449_);
lean_dec(v_s_1447_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v_state_1454_; lean_object* v___x_1456_; 
v_state_1454_ = lean_apply_2(v_addEntryFn_1448_, v_state_1450_, v_entry_1446_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 1, v_state_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_importedEntries_1449_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_state_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
return v___x_1462_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1463_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__5));
v___x_1469_ = l_Lean_stringToMessageData(v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__7));
v___x_1472_ = l_Lean_stringToMessageData(v___x_1471_);
return v___x_1472_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1));
v___x_1474_ = l_Lean_stringToMessageData(v___x_1473_);
return v___x_1474_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_cls_1475_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__4));
v___x_1476_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__1));
v___x_1477_ = l_Lean_Name_append(v___x_1476_, v_cls_1475_);
return v___x_1477_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__11));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__13));
v___x_1483_ = l_Lean_stringToMessageData(v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(lean_object* v_mod_1488_, uint8_t v_isMeta_1489_, lean_object* v_hint_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v_env_1512_; uint8_t v_isExporting_1513_; lean_object* v_entry_1514_; lean_object* v___x_1515_; lean_object* v_env_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1510_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2);
v___x_1511_ = lean_st_ref_get(v___y_1492_);
v_env_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc_ref(v_env_1512_);
lean_dec(v___x_1511_);
v_isExporting_1513_ = lean_ctor_get_uint8(v_env_1512_, sizeof(void*)*13);
lean_dec_ref(v_env_1512_);
lean_inc(v_mod_1488_);
v_entry_1514_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1514_, 0, v_mod_1488_);
lean_ctor_set_uint8(v_entry_1514_, sizeof(void*)*1, v_isExporting_1513_);
lean_ctor_set_uint8(v_entry_1514_, sizeof(void*)*1 + 1, v_isMeta_1489_);
v___x_1515_ = lean_st_ref_get(v___y_1492_);
v_env_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc_ref(v_env_1516_);
lean_dec(v___x_1515_);
v___x_1517_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1518_ = lean_box(1);
v___x_1519_ = lean_box(0);
v___x_1520_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1510_, v___x_1517_, v_env_1516_, v___x_1518_, v___x_1519_);
v___x_1521_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(v___x_1520_, v_entry_1514_);
lean_dec(v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v_toCold_1522_; lean_object* v_options_1523_; lean_object* v_inheritedTraceOptions_1524_; uint8_t v_hasTrace_1525_; lean_object* v___f_1526_; uint8_t v___x_1527_; lean_object* v___y_1529_; 
v_toCold_1522_ = lean_ctor_get(v___y_1491_, 0);
v_options_1523_ = lean_ctor_get(v_toCold_1522_, 2);
v_inheritedTraceOptions_1524_ = lean_ctor_get(v_toCold_1522_, 11);
v_hasTrace_1525_ = lean_ctor_get_uint8(v_options_1523_, sizeof(void*)*1);
v___f_1526_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_1526_, 0, v___x_1517_);
lean_closure_set(v___f_1526_, 1, v_entry_1514_);
v___x_1527_ = 1;
if (v_hasTrace_1525_ == 0)
{
lean_dec(v_hint_1490_);
lean_dec(v_mod_1488_);
v___y_1529_ = v___y_1492_;
goto v___jp_1528_;
}
else
{
lean_object* v_cls_1547_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v_cls_1547_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__4));
v___x_1567_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10);
v___x_1568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1524_, v_options_1523_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_dec(v_hint_1490_);
lean_dec(v_mod_1488_);
v___y_1529_ = v___y_1492_;
goto v___jp_1528_;
}
else
{
lean_object* v___x_1569_; lean_object* v___y_1571_; 
v___x_1569_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12);
if (v_isExporting_1513_ == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__17));
v___y_1571_ = v___x_1578_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__18));
v___y_1571_ = v___x_1579_;
goto v___jp_1570_;
}
v___jp_1570_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_inc_ref(v___y_1571_);
v___x_1572_ = l_Lean_stringToMessageData(v___y_1571_);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1569_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
if (v_isMeta_1489_ == 0)
{
lean_object* v___x_1576_; 
v___x_1576_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__15));
v___y_1554_ = v___x_1575_;
v___y_1555_ = v___x_1576_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1577_; 
v___x_1577_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__16));
v___y_1554_ = v___x_1575_;
v___y_1555_ = v___x_1577_;
goto v___jp_1553_;
}
}
}
v___jp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___y_1549_);
lean_ctor_set(v___x_1551_, 1, v___y_1550_);
v___x_1552_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(v_cls_1547_, v___x_1551_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_dec_ref_known(v___x_1552_, 1);
v___y_1529_ = v___y_1492_;
goto v___jp_1528_;
}
else
{
lean_dec_ref(v___f_1526_);
return v___x_1552_;
}
}
v___jp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
lean_inc_ref(v___y_1555_);
v___x_1556_ = l_Lean_stringToMessageData(v___y_1555_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___y_1554_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_MessageData_ofName(v_mod_1488_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_Name_isAnonymous(v_hint_1490_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8);
v___x_1564_ = l_Lean_MessageData_ofName(v_hint_1490_);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___y_1549_ = v___x_1561_;
v___y_1550_ = v___x_1565_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1566_; 
lean_dec(v_hint_1490_);
v___x_1566_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9);
v___y_1549_ = v___x_1561_;
v___y_1550_ = v___x_1566_;
goto v___jp_1548_;
}
}
}
v___jp_1528_:
{
lean_object* v___x_1530_; lean_object* v_toEnvExtension_1531_; lean_object* v_env_1532_; lean_object* v_nextMacroScope_1533_; lean_object* v_ngen_1534_; lean_object* v_auxDeclNGen_1535_; lean_object* v_traceState_1536_; lean_object* v_recordedDeps_1537_; lean_object* v_messages_1538_; lean_object* v_infoState_1539_; lean_object* v_snapshotTasks_1540_; lean_object* v_asyncMode_1541_; uint8_t v_logWrites_1542_; lean_object* v___x_1543_; 
v___x_1530_ = lean_st_ref_take(v___y_1529_);
v_toEnvExtension_1531_ = lean_ctor_get(v___x_1517_, 0);
v_env_1532_ = lean_ctor_get(v___x_1530_, 0);
lean_inc_ref(v_env_1532_);
v_nextMacroScope_1533_ = lean_ctor_get(v___x_1530_, 1);
lean_inc(v_nextMacroScope_1533_);
v_ngen_1534_ = lean_ctor_get(v___x_1530_, 2);
lean_inc_ref(v_ngen_1534_);
v_auxDeclNGen_1535_ = lean_ctor_get(v___x_1530_, 3);
lean_inc_ref(v_auxDeclNGen_1535_);
v_traceState_1536_ = lean_ctor_get(v___x_1530_, 4);
lean_inc_ref(v_traceState_1536_);
v_recordedDeps_1537_ = lean_ctor_get(v___x_1530_, 6);
lean_inc_ref(v_recordedDeps_1537_);
v_messages_1538_ = lean_ctor_get(v___x_1530_, 7);
lean_inc_ref(v_messages_1538_);
v_infoState_1539_ = lean_ctor_get(v___x_1530_, 8);
lean_inc_ref(v_infoState_1539_);
v_snapshotTasks_1540_ = lean_ctor_get(v___x_1530_, 9);
lean_inc_ref(v_snapshotTasks_1540_);
lean_dec(v___x_1530_);
v_asyncMode_1541_ = lean_ctor_get(v_toEnvExtension_1531_, 2);
v_logWrites_1542_ = lean_ctor_get_uint8(v_toEnvExtension_1531_, sizeof(void*)*6);
v___x_1543_ = lean_box(0);
if (v_logWrites_1542_ == 0)
{
lean_object* v___x_1544_; 
lean_inc_ref(v_toEnvExtension_1531_);
v___x_1544_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1531_, v_env_1532_, v___f_1526_, v_asyncMode_1541_, v___x_1519_, v___x_1527_);
v___y_1495_ = v___y_1529_;
v___y_1496_ = v_nextMacroScope_1533_;
v___y_1497_ = v_infoState_1539_;
v___y_1498_ = v_ngen_1534_;
v___y_1499_ = v_messages_1538_;
v___y_1500_ = v_recordedDeps_1537_;
v___y_1501_ = v_traceState_1536_;
v___y_1502_ = v_auxDeclNGen_1535_;
v___y_1503_ = v_snapshotTasks_1540_;
v___y_1504_ = v___x_1543_;
v___y_1505_ = v___x_1544_;
goto v___jp_1494_;
}
else
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_inc_ref_n(v_toEnvExtension_1531_, 2);
v___x_1545_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1531_, v_env_1532_);
lean_dec_ref(v_env_1532_);
v___x_1546_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1531_, v___x_1545_, v___f_1526_, v_asyncMode_1541_, v___x_1519_, v___x_1527_);
v___y_1495_ = v___y_1529_;
v___y_1496_ = v_nextMacroScope_1533_;
v___y_1497_ = v_infoState_1539_;
v___y_1498_ = v_ngen_1534_;
v___y_1499_ = v_messages_1538_;
v___y_1500_ = v_recordedDeps_1537_;
v___y_1501_ = v_traceState_1536_;
v___y_1502_ = v_auxDeclNGen_1535_;
v___y_1503_ = v_snapshotTasks_1540_;
v___y_1504_ = v___x_1543_;
v___y_1505_ = v___x_1546_;
goto v___jp_1494_;
}
}
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec_ref_known(v_entry_1514_, 1);
lean_dec(v_hint_1490_);
lean_dec(v_mod_1488_);
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
v___jp_1494_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1506_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1);
v___x_1507_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1507_, 0, v___y_1505_);
lean_ctor_set(v___x_1507_, 1, v___y_1496_);
lean_ctor_set(v___x_1507_, 2, v___y_1498_);
lean_ctor_set(v___x_1507_, 3, v___y_1502_);
lean_ctor_set(v___x_1507_, 4, v___y_1501_);
lean_ctor_set(v___x_1507_, 5, v___x_1506_);
lean_ctor_set(v___x_1507_, 6, v___y_1500_);
lean_ctor_set(v___x_1507_, 7, v___y_1499_);
lean_ctor_set(v___x_1507_, 8, v___y_1497_);
lean_ctor_set(v___x_1507_, 9, v___y_1503_);
v___x_1508_ = lean_st_ref_put(v___y_1495_, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___y_1504_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_1582_, lean_object* v_isMeta_1583_, lean_object* v_hint_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
uint8_t v_isMeta_boxed_1588_; lean_object* v_res_1589_; 
v_isMeta_boxed_1588_ = lean_unbox(v_isMeta_1583_);
v_res_1589_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(v_mod_1582_, v_isMeta_boxed_1588_, v_hint_1584_, v___y_1585_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(lean_object* v_a_1590_, lean_object* v_x_1591_){
_start:
{
if (lean_obj_tag(v_x_1591_) == 0)
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_box(0);
return v___x_1592_;
}
else
{
lean_object* v_key_1593_; lean_object* v_value_1594_; lean_object* v_tail_1595_; uint8_t v___x_1596_; 
v_key_1593_ = lean_ctor_get(v_x_1591_, 0);
v_value_1594_ = lean_ctor_get(v_x_1591_, 1);
v_tail_1595_ = lean_ctor_get(v_x_1591_, 2);
v___x_1596_ = lean_name_eq(v_key_1593_, v_a_1590_);
if (v___x_1596_ == 0)
{
v_x_1591_ = v_tail_1595_;
goto _start;
}
else
{
lean_object* v___x_1598_; 
lean_inc(v_value_1594_);
v___x_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1598_, 0, v_value_1594_);
return v___x_1598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_a_1599_, lean_object* v_x_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(v_a_1599_, v_x_1600_);
lean_dec(v_x_1600_);
lean_dec(v_a_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(lean_object* v_m_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v_buckets_1604_; lean_object* v___x_1605_; uint64_t v___y_1607_; 
v_buckets_1604_ = lean_ctor_get(v_m_1602_, 1);
v___x_1605_ = lean_array_get_size(v_buckets_1604_);
if (lean_obj_tag(v_a_1603_) == 0)
{
uint64_t v___x_1621_; 
v___x_1621_ = 1723ULL;
v___y_1607_ = v___x_1621_;
goto v___jp_1606_;
}
else
{
uint64_t v_hash_1622_; 
v_hash_1622_ = lean_ctor_get_uint64(v_a_1603_, sizeof(void*)*2);
v___y_1607_ = v_hash_1622_;
goto v___jp_1606_;
}
v___jp_1606_:
{
uint64_t v___x_1608_; uint64_t v___x_1609_; uint64_t v_fold_1610_; uint64_t v___x_1611_; uint64_t v___x_1612_; uint64_t v___x_1613_; size_t v___x_1614_; size_t v___x_1615_; size_t v___x_1616_; size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1608_ = 32ULL;
v___x_1609_ = lean_uint64_shift_right(v___y_1607_, v___x_1608_);
v_fold_1610_ = lean_uint64_xor(v___y_1607_, v___x_1609_);
v___x_1611_ = 16ULL;
v___x_1612_ = lean_uint64_shift_right(v_fold_1610_, v___x_1611_);
v___x_1613_ = lean_uint64_xor(v_fold_1610_, v___x_1612_);
v___x_1614_ = lean_uint64_to_usize(v___x_1613_);
v___x_1615_ = lean_usize_of_nat(v___x_1605_);
v___x_1616_ = ((size_t)1ULL);
v___x_1617_ = lean_usize_sub(v___x_1615_, v___x_1616_);
v___x_1618_ = lean_usize_land(v___x_1614_, v___x_1617_);
v___x_1619_ = lean_array_uget_borrowed(v_buckets_1604_, v___x_1618_);
v___x_1620_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(v_a_1603_, v___x_1619_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(v_m_1623_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_m_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4(lean_object* v___x_1626_, lean_object* v_declName_1627_, lean_object* v_as_1628_, size_t v_sz_1629_, size_t v_i_1630_, lean_object* v_b_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v___x_1635_; 
v___x_1635_ = lean_usize_dec_lt(v_i_1630_, v_sz_1629_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; 
lean_dec(v_declName_1627_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_b_1631_);
return v___x_1636_;
}
else
{
lean_object* v___x_1637_; lean_object* v_modules_1638_; lean_object* v___x_1639_; lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v_toImport_1642_; lean_object* v_module_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; lean_object* v___x_1646_; 
v___x_1637_ = l_Lean_Environment_header(v___x_1626_);
v_modules_1638_ = lean_ctor_get(v___x_1637_, 3);
lean_inc_ref(v_modules_1638_);
lean_dec_ref(v___x_1637_);
v___x_1639_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1640_ = lean_array_uget_borrowed(v_as_1628_, v_i_1630_);
v___x_1641_ = lean_array_get(v___x_1639_, v_modules_1638_, v_a_1640_);
lean_dec_ref(v_modules_1638_);
v_toImport_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc_ref(v_toImport_1642_);
lean_dec(v___x_1641_);
v_module_1643_ = lean_ctor_get(v_toImport_1642_, 0);
lean_inc(v_module_1643_);
lean_dec_ref(v_toImport_1642_);
v___x_1644_ = lean_box(0);
v___x_1645_ = 0;
lean_inc(v_declName_1627_);
v___x_1646_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(v_module_1643_, v___x_1645_, v_declName_1627_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1646_) == 0)
{
size_t v___x_1647_; size_t v___x_1648_; 
lean_dec_ref_known(v___x_1646_, 1);
v___x_1647_ = ((size_t)1ULL);
v___x_1648_ = lean_usize_add(v_i_1630_, v___x_1647_);
v_i_1630_ = v___x_1648_;
v_b_1631_ = v___x_1644_;
goto _start;
}
else
{
lean_dec(v_declName_1627_);
return v___x_1646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4___boxed(lean_object* v___x_1650_, lean_object* v_declName_1651_, lean_object* v_as_1652_, lean_object* v_sz_1653_, lean_object* v_i_1654_, lean_object* v_b_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
size_t v_sz_boxed_1659_; size_t v_i_boxed_1660_; lean_object* v_res_1661_; 
v_sz_boxed_1659_ = lean_unbox_usize(v_sz_1653_);
lean_dec(v_sz_1653_);
v_i_boxed_1660_ = lean_unbox_usize(v_i_1654_);
lean_dec(v_i_1654_);
v_res_1661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4(v___x_1650_, v_declName_1651_, v_as_1652_, v_sz_boxed_1659_, v_i_boxed_1660_, v_b_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec_ref(v_as_1652_);
lean_dec_ref(v___x_1650_);
return v_res_1661_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2(lean_object* v_declName_1665_, uint8_t v_isMeta_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v_env_1675_; lean_object* v___y_1677_; lean_object* v___x_1690_; 
v___x_1670_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0);
v___x_1671_ = lean_st_ref_get(v___y_1668_);
v_env_1675_ = lean_ctor_get(v___x_1671_, 0);
lean_inc_ref(v_env_1675_);
lean_dec(v___x_1671_);
v___x_1690_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1675_, v_declName_1665_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_dec_ref(v_env_1675_);
lean_dec(v_declName_1665_);
goto v___jp_1672_;
}
else
{
lean_object* v_val_1691_; lean_object* v___x_1692_; lean_object* v_modules_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_val_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = l_Lean_Environment_header(v_env_1675_);
v_modules_1693_ = lean_ctor_get(v___x_1692_, 3);
lean_inc_ref(v_modules_1693_);
lean_dec_ref(v___x_1692_);
v___x_1694_ = lean_array_get_size(v_modules_1693_);
v___x_1695_ = lean_nat_dec_lt(v_val_1691_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_dec_ref(v_modules_1693_);
lean_dec(v_val_1691_);
lean_dec_ref(v_env_1675_);
lean_dec(v_declName_1665_);
goto v___jp_1672_;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___y_1699_; 
v___x_1696_ = lean_array_fget(v_modules_1693_, v_val_1691_);
lean_dec(v_val_1691_);
lean_dec_ref(v_modules_1693_);
v___x_1697_ = lean_st_ref_get(v___y_1668_);
if (v_isMeta_1666_ == 0)
{
lean_dec(v___x_1697_);
v___y_1699_ = v_isMeta_1666_;
goto v___jp_1698_;
}
else
{
lean_object* v_env_1710_; uint8_t v___x_1711_; 
v_env_1710_ = lean_ctor_get(v___x_1697_, 0);
lean_inc_ref(v_env_1710_);
lean_dec(v___x_1697_);
lean_inc(v_declName_1665_);
v___x_1711_ = l_Lean_isMarkedMeta(v_env_1710_, v_declName_1665_);
if (v___x_1711_ == 0)
{
v___y_1699_ = v_isMeta_1666_;
goto v___jp_1698_;
}
else
{
uint8_t v___x_1712_; 
v___x_1712_ = 0;
v___y_1699_ = v___x_1712_;
goto v___jp_1698_;
}
}
v___jp_1698_:
{
lean_object* v_toImport_1700_; lean_object* v_module_1701_; lean_object* v___x_1702_; 
v_toImport_1700_ = lean_ctor_get(v___x_1696_, 0);
lean_inc_ref(v_toImport_1700_);
lean_dec(v___x_1696_);
v_module_1701_ = lean_ctor_get(v_toImport_1700_, 0);
lean_inc(v_module_1701_);
lean_dec_ref(v_toImport_1700_);
lean_inc(v_declName_1665_);
v___x_1702_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(v_module_1701_, v___y_1699_, v_declName_1665_, v___y_1667_, v___y_1668_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec_ref_known(v___x_1702_, 1);
v___x_1703_ = l_Lean_indirectModUseExt;
v___x_1704_ = lean_box(1);
v___x_1705_ = lean_box(0);
lean_inc_ref(v_env_1675_);
v___x_1706_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1670_, v___x_1703_, v_env_1675_, v___x_1704_, v___x_1705_);
v___x_1707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(v___x_1706_, v_declName_1665_);
lean_dec(v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1708_; 
v___x_1708_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__1));
v___y_1677_ = v___x_1708_;
goto v___jp_1676_;
}
else
{
lean_object* v_val_1709_; 
v_val_1709_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v___x_1707_, 1);
v___y_1677_ = v_val_1709_;
goto v___jp_1676_;
}
}
else
{
lean_dec_ref(v_env_1675_);
lean_dec(v_declName_1665_);
return v___x_1702_;
}
}
}
}
v___jp_1672_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_box(0);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
v___jp_1676_:
{
lean_object* v___x_1678_; size_t v_sz_1679_; size_t v___x_1680_; lean_object* v___x_1681_; 
v___x_1678_ = lean_box(0);
v_sz_1679_ = lean_array_size(v___y_1677_);
v___x_1680_ = ((size_t)0ULL);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4(v_env_1675_, v_declName_1665_, v___y_1677_, v_sz_1679_, v___x_1680_, v___x_1678_, v___y_1667_, v___y_1668_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_env_1675_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v___x_1681_, 0);
lean_dec(v_unused_1689_);
v___x_1683_ = v___x_1681_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_dec(v___x_1681_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1678_);
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1678_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
return v___x_1681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___boxed(lean_object* v_declName_1713_, lean_object* v_isMeta_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
uint8_t v_isMeta_boxed_1718_; lean_object* v_res_1719_; 
v_isMeta_boxed_1718_ = lean_unbox(v_isMeta_1714_);
v_res_1719_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2(v_declName_1713_, v_isMeta_boxed_1718_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(lean_object* v_as_x27_1720_, lean_object* v_b_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
if (lean_obj_tag(v_as_x27_1720_) == 0)
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_b_1721_);
return v___x_1725_;
}
else
{
lean_object* v_head_1726_; lean_object* v_tail_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; lean_object* v___x_1730_; 
v_head_1726_ = lean_ctor_get(v_as_x27_1720_, 0);
v_tail_1727_ = lean_ctor_get(v_as_x27_1720_, 1);
v___x_1728_ = lean_box(0);
v___x_1729_ = 1;
lean_inc(v_head_1726_);
v___x_1730_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2(v_head_1726_, v___x_1729_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_dec_ref_known(v___x_1730_, 1);
v_as_x27_1720_ = v_tail_1727_;
v_b_1721_ = v___x_1728_;
goto _start;
}
else
{
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1732_, lean_object* v_b_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(v_as_x27_1732_, v_b_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v_as_x27_1732_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(lean_object* v_x_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; lean_object* v_toCold_1744_; lean_object* v_env_1745_; lean_object* v_currRecDepth_1746_; lean_object* v_ref_1747_; lean_object* v_maxRecDepth_1748_; lean_object* v_currNamespace_1749_; lean_object* v_openDecls_1750_; lean_object* v_quotContext_1751_; lean_object* v_currMacroScope_1752_; lean_object* v___f_1753_; lean_object* v___f_1754_; lean_object* v___x_1755_; lean_object* v___f_1756_; lean_object* v___f_1757_; lean_object* v___f_1758_; lean_object* v_methods_1759_; lean_object* v___x_1760_; lean_object* v_nextMacroScope_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1743_ = lean_st_ref_get(v___y_1741_);
v_toCold_1744_ = lean_ctor_get(v___y_1740_, 0);
v_env_1745_ = lean_ctor_get(v___x_1743_, 0);
lean_inc_ref_n(v_env_1745_, 4);
lean_dec(v___x_1743_);
v_currRecDepth_1746_ = lean_ctor_get(v___y_1740_, 1);
v_ref_1747_ = lean_ctor_get(v___y_1740_, 2);
v_maxRecDepth_1748_ = lean_ctor_get(v_toCold_1744_, 3);
v_currNamespace_1749_ = lean_ctor_get(v_toCold_1744_, 4);
v_openDecls_1750_ = lean_ctor_get(v_toCold_1744_, 5);
v_quotContext_1751_ = lean_ctor_get(v_toCold_1744_, 8);
v_currMacroScope_1752_ = lean_ctor_get(v_toCold_1744_, 9);
v___f_1753_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1753_, 0, v_env_1745_);
v___f_1754_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2___boxed), 4, 1);
lean_closure_set(v___f_1754_, 0, v_env_1745_);
v___x_1755_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1740_);
lean_inc_n(v_currNamespace_1749_, 3);
v___f_1756_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1756_, 0, v_currNamespace_1749_);
lean_inc_n(v_openDecls_1750_, 2);
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1757_, 0, v_env_1745_);
lean_closure_set(v___f_1757_, 1, v___x_1755_);
lean_closure_set(v___f_1757_, 2, v_currNamespace_1749_);
lean_closure_set(v___f_1757_, 3, v_openDecls_1750_);
v___f_1758_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1758_, 0, v_env_1745_);
lean_closure_set(v___f_1758_, 1, v_currNamespace_1749_);
lean_closure_set(v___f_1758_, 2, v_openDecls_1750_);
v_methods_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1759_, 0, v___f_1754_);
lean_ctor_set(v_methods_1759_, 1, v___f_1756_);
lean_ctor_set(v_methods_1759_, 2, v___f_1753_);
lean_ctor_set(v_methods_1759_, 3, v___f_1758_);
lean_ctor_set(v_methods_1759_, 4, v___f_1757_);
v___x_1760_ = lean_st_ref_get(v___y_1741_);
v_nextMacroScope_1761_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_nextMacroScope_1761_);
lean_dec(v___x_1760_);
lean_inc(v_ref_1747_);
lean_inc(v_maxRecDepth_1748_);
lean_inc(v_currRecDepth_1746_);
lean_inc(v_currMacroScope_1752_);
lean_inc(v_quotContext_1751_);
v___x_1762_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1762_, 0, v_methods_1759_);
lean_ctor_set(v___x_1762_, 1, v_quotContext_1751_);
lean_ctor_set(v___x_1762_, 2, v_currMacroScope_1752_);
lean_ctor_set(v___x_1762_, 3, v_currRecDepth_1746_);
lean_ctor_set(v___x_1762_, 4, v_maxRecDepth_1748_);
lean_ctor_set(v___x_1762_, 5, v_ref_1747_);
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1764_, 0, v_nextMacroScope_1761_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
lean_ctor_set(v___x_1764_, 2, v___x_1763_);
v___x_1765_ = lean_apply_2(v_x_1739_, v___x_1762_, v___x_1764_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v_a_1767_; lean_object* v_macroScope_1768_; lean_object* v_traceMsgs_1769_; lean_object* v_expandedMacroDecls_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 1);
lean_inc(v_a_1766_);
v_a_1767_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1765_, 2);
v_macroScope_1768_ = lean_ctor_get(v_a_1766_, 0);
lean_inc(v_macroScope_1768_);
v_traceMsgs_1769_ = lean_ctor_get(v_a_1766_, 1);
lean_inc(v_traceMsgs_1769_);
v_expandedMacroDecls_1770_ = lean_ctor_get(v_a_1766_, 2);
lean_inc(v_expandedMacroDecls_1770_);
lean_dec(v_a_1766_);
v___x_1771_ = lean_box(0);
v___x_1772_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(v_expandedMacroDecls_1770_, v___x_1771_, v___y_1740_, v___y_1741_);
lean_dec(v_expandedMacroDecls_1770_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v___x_1773_; lean_object* v_env_1774_; lean_object* v_ngen_1775_; lean_object* v_auxDeclNGen_1776_; lean_object* v_traceState_1777_; lean_object* v_cache_1778_; lean_object* v_recordedDeps_1779_; lean_object* v_messages_1780_; lean_object* v_infoState_1781_; lean_object* v_snapshotTasks_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref_known(v___x_1772_, 1);
v___x_1773_ = lean_st_ref_take(v___y_1741_);
v_env_1774_ = lean_ctor_get(v___x_1773_, 0);
v_ngen_1775_ = lean_ctor_get(v___x_1773_, 2);
v_auxDeclNGen_1776_ = lean_ctor_get(v___x_1773_, 3);
v_traceState_1777_ = lean_ctor_get(v___x_1773_, 4);
v_cache_1778_ = lean_ctor_get(v___x_1773_, 5);
v_recordedDeps_1779_ = lean_ctor_get(v___x_1773_, 6);
v_messages_1780_ = lean_ctor_get(v___x_1773_, 7);
v_infoState_1781_ = lean_ctor_get(v___x_1773_, 8);
v_snapshotTasks_1782_ = lean_ctor_get(v___x_1773_, 9);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v___x_1773_, 1);
lean_dec(v_unused_1809_);
v___x_1784_ = v___x_1773_;
v_isShared_1785_ = v_isSharedCheck_1808_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snapshotTasks_1782_);
lean_inc(v_infoState_1781_);
lean_inc(v_messages_1780_);
lean_inc(v_recordedDeps_1779_);
lean_inc(v_cache_1778_);
lean_inc(v_traceState_1777_);
lean_inc(v_auxDeclNGen_1776_);
lean_inc(v_ngen_1775_);
lean_inc(v_env_1774_);
lean_dec(v___x_1773_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1808_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 1, v_macroScope_1768_);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_env_1774_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_macroScope_1768_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_ngen_1775_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_auxDeclNGen_1776_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_traceState_1777_);
lean_ctor_set(v_reuseFailAlloc_1807_, 5, v_cache_1778_);
lean_ctor_set(v_reuseFailAlloc_1807_, 6, v_recordedDeps_1779_);
lean_ctor_set(v_reuseFailAlloc_1807_, 7, v_messages_1780_);
lean_ctor_set(v_reuseFailAlloc_1807_, 8, v_infoState_1781_);
lean_ctor_set(v_reuseFailAlloc_1807_, 9, v_snapshotTasks_1782_);
v___x_1787_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = lean_st_ref_put(v___y_1741_, v___x_1787_);
v___x_1789_ = l_List_reverse___redArg(v_traceMsgs_1769_);
v___x_1790_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4(v___x_1789_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v___x_1790_, 0);
lean_dec(v_unused_1798_);
v___x_1792_ = v___x_1790_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_dec(v___x_1790_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v_a_1767_);
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1767_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_a_1767_);
v_a_1799_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1790_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1790_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_traceMsgs_1769_);
lean_dec(v_macroScope_1768_);
lean_dec(v_a_1767_);
v_a_1810_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1772_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1772_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_object* v_a_1818_; 
v_a_1818_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1765_, 2);
if (lean_obj_tag(v_a_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v_a_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v_a_1819_ = lean_ctor_get(v_a_1818_, 0);
lean_inc(v_a_1819_);
v_a_1820_ = lean_ctor_get(v_a_1818_, 1);
lean_inc_ref(v_a_1820_);
lean_dec_ref_known(v_a_1818_, 2);
v___x_1821_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___closed__0));
v___x_1822_ = lean_string_dec_eq(v_a_1820_, v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_a_1820_);
v___x_1824_ = l_Lean_MessageData_ofFormat(v___x_1823_);
v___x_1825_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(v_a_1819_, v___x_1824_, v___y_1740_, v___y_1741_);
lean_dec(v_a_1819_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; 
lean_dec_ref(v_a_1820_);
v___x_1826_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(v_a_1819_);
return v___x_1826_;
}
}
else
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg();
return v___x_1827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___boxed(lean_object* v_x_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(v_x_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
return v_res_1832_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__1));
v___x_1837_ = l_Lean_MessageData_ofFormat(v___x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(lean_object* v_stx_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v___y_1843_; lean_object* v_a_1844_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_env_1853_; lean_object* v___x_1854_; lean_object* v_toEnvExtension_1855_; lean_object* v_asyncMode_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1848_ = lean_box(1);
v___x_1849_ = lean_st_ref_get(v_a_1840_);
v_env_1853_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_ref_n(v_env_1853_, 2);
lean_dec(v___x_1849_);
v___x_1854_ = l_Lean_Elab_deprecatedSyntaxReplacementExt;
v_toEnvExtension_1855_ = lean_ctor_get(v___x_1854_, 0);
v_asyncMode_1856_ = lean_ctor_get(v_toEnvExtension_1855_, 2);
v___x_1857_ = lean_box(0);
v___x_1858_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1848_, v___x_1854_, v_env_1853_, v_asyncMode_1856_, v___x_1857_);
lean_inc(v_stx_1838_);
v___x_1859_ = l_Lean_Syntax_getKind(v_stx_1838_);
v___x_1860_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1858_, v___x_1859_);
lean_dec(v___x_1858_);
if (lean_obj_tag(v___x_1860_) == 1)
{
lean_object* v_val_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1965_; 
v_val_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1965_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_val_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1965_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1865_ = l_Lean_Parser_getSyntaxNodeKindCategories(v_env_1853_, v___x_1859_);
v___x_1866_ = lean_array_get_size(v___x_1865_);
v___x_1867_ = lean_unsigned_to_nat(1u);
v___x_1868_ = lean_nat_dec_eq(v___x_1866_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_dec_ref(v___x_1865_);
lean_dec(v_val_1861_);
lean_dec(v_stx_1838_);
v___x_1869_ = l_Lean_MessageData_nil;
if (v_isShared_1864_ == 0)
{
lean_ctor_set_tag(v___x_1863_, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1869_);
v___x_1871_ = v___x_1863_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
else
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_Syntax_getRange_x3f(v_stx_1838_, v___x_1868_);
if (lean_obj_tag(v___x_1873_) == 1)
{
lean_object* v_toCold_1874_; lean_object* v_val_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1960_; 
lean_del_object(v___x_1863_);
v_toCold_1874_ = lean_ctor_get(v_a_1839_, 0);
v_val_1875_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1877_ = v___x_1873_;
v_isShared_1878_ = v_isSharedCheck_1960_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_val_1875_);
lean_dec(v___x_1873_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1960_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_currRecDepth_1879_; lean_object* v_ref_1880_; uint16_t v_optionFlags_1881_; uint8_t v_suppressElabErrors_1882_; uint8_t v_checkDeprecated_1883_; uint8_t v_isRecordingDeps_1884_; lean_object* v_fileMap_1885_; lean_object* v___x_1886_; 
v_currRecDepth_1879_ = lean_ctor_get(v_a_1839_, 1);
v_ref_1880_ = lean_ctor_get(v_a_1839_, 2);
v_optionFlags_1881_ = lean_ctor_get_uint16(v_a_1839_, sizeof(void*)*3);
v_suppressElabErrors_1882_ = lean_ctor_get_uint8(v_a_1839_, sizeof(void*)*3 + 2);
v_checkDeprecated_1883_ = lean_ctor_get_uint8(v_a_1839_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1884_ = lean_ctor_get_uint8(v_a_1839_, sizeof(void*)*3 + 4);
v_fileMap_1885_ = lean_ctor_get(v_toCold_1874_, 1);
v___x_1886_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1838_, v___x_1868_, v___x_1868_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_del_object(v___x_1877_);
lean_dec(v_val_1875_);
lean_dec_ref(v___x_1865_);
lean_dec(v_val_1861_);
lean_dec(v_stx_1838_);
goto v___jp_1850_;
}
else
{
lean_object* v_val_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1959_; 
v_val_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1959_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_val_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1959_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_str_1891_; lean_object* v_source_1892_; uint8_t v___x_1893_; 
v_str_1891_ = lean_ctor_get(v_val_1887_, 0);
lean_inc_ref(v_str_1891_);
lean_dec(v_val_1887_);
v_source_1892_ = lean_ctor_get(v_fileMap_1885_, 0);
v___x_1893_ = lean_string_dec_eq(v_str_1891_, v_source_1892_);
lean_dec_ref(v_str_1891_);
if (v___x_1893_ == 0)
{
lean_del_object(v___x_1889_);
lean_del_object(v___x_1877_);
lean_dec(v_val_1875_);
lean_dec_ref(v___x_1865_);
lean_dec(v_val_1861_);
lean_dec(v_stx_1838_);
goto v___jp_1850_;
}
else
{
lean_object* v___x_1894_; lean_object* v___f_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_box(v___x_1893_);
v___f_1895_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1895_, 0, v___x_1894_);
lean_inc(v_stx_1838_);
v___x_1896_ = l_Lean_Syntax_find_x3f(v_stx_1838_, v___f_1895_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_array_fget(v___x_1865_, v___x_1897_);
lean_dec_ref(v___x_1865_);
v___x_1899_ = 0;
v___x_1900_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe(v_val_1861_, v_a_1839_, v_a_1840_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_ref_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
lean_inc(v_stx_1838_);
v___x_1902_ = l_Lean_Syntax_unsetTrailing(v_stx_1838_);
v___x_1903_ = lean_apply_1(v_a_1901_, v___x_1902_);
v_ref_1904_ = l_Lean_replaceRef(v_stx_1838_, v_ref_1880_);
lean_inc(v_currRecDepth_1879_);
lean_inc_ref(v_toCold_1874_);
v___x_1905_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1905_, 0, v_toCold_1874_);
lean_ctor_set(v___x_1905_, 1, v_currRecDepth_1879_);
lean_ctor_set(v___x_1905_, 2, v_ref_1904_);
lean_ctor_set_uint16(v___x_1905_, sizeof(void*)*3, v_optionFlags_1881_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*3 + 2, v_suppressElabErrors_1882_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*3 + 3, v_checkDeprecated_1883_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*3 + 4, v_isRecordingDeps_1884_);
v___x_1906_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(v___x_1903_, v___x_1905_, v_a_1840_);
lean_dec_ref_known(v___x_1905_, 3);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = l_Lean_Syntax_eraseQuoteMacroScopes(v_a_1907_);
lean_inc(v_stx_1838_);
v___x_1909_ = l_Lean_Elab_DeprecatedSyntax_formatReplacement(v___x_1898_, v_stx_1838_, v___x_1908_, v_val_1875_, v_a_1839_, v_a_1840_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2, &l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2_once, _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v_a_1910_);
v___x_1913_ = v___x_1877_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1910_);
v___x_1913_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1914_ = lean_box(0);
v___x_1915_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
lean_ctor_set(v___x_1915_, 2, v___x_1914_);
lean_ctor_set(v___x_1915_, 3, v___x_1914_);
lean_ctor_set(v___x_1915_, 4, v___x_1914_);
lean_ctor_set(v___x_1915_, 5, v___x_1914_);
v___x_1916_ = 0;
v___x_1917_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1896_);
lean_ctor_set(v___x_1917_, 2, v___x_1896_);
lean_ctor_set_uint8(v___x_1917_, sizeof(void*)*3, v___x_1916_);
v___x_1918_ = lean_mk_empty_array_with_capacity(v___x_1867_);
v___x_1919_ = lean_array_push(v___x_1918_, v___x_1917_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v_stx_1838_);
v___x_1921_ = v___x_1889_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_stx_1838_);
v___x_1921_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_MessageData_hint(v___x_1911_, v___x_1919_, v___x_1921_, v___x_1914_, v___x_1899_, v_a_1839_, v_a_1840_);
lean_dec_ref(v___x_1919_);
if (lean_obj_tag(v___x_1922_) == 0)
{
return v___x_1922_;
}
else
{
lean_object* v_a_1923_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
v___y_1843_ = v___x_1922_;
v_a_1844_ = v_a_1923_;
goto v___jp_1842_;
}
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_del_object(v___x_1889_);
lean_del_object(v___x_1877_);
lean_dec(v_stx_1838_);
v_a_1926_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1909_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1909_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
lean_inc(v_a_1926_);
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
v___y_1843_ = v___x_1931_;
v_a_1844_ = v_a_1926_;
goto v___jp_1842_;
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec(v___x_1898_);
lean_del_object(v___x_1889_);
lean_del_object(v___x_1877_);
lean_dec(v_val_1875_);
lean_dec(v_stx_1838_);
v_a_1934_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1906_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1906_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
lean_inc(v_a_1934_);
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
v___y_1843_ = v___x_1939_;
v_a_1844_ = v_a_1934_;
goto v___jp_1842_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v___x_1898_);
lean_del_object(v___x_1889_);
lean_del_object(v___x_1877_);
lean_dec(v_val_1875_);
lean_dec(v_stx_1838_);
v_a_1942_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1900_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1900_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
lean_inc(v_a_1942_);
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
v___y_1843_ = v___x_1947_;
v_a_1844_ = v_a_1942_;
goto v___jp_1842_;
}
}
}
}
else
{
lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1957_; 
lean_del_object(v___x_1889_);
lean_del_object(v___x_1877_);
lean_dec(v_val_1875_);
lean_dec_ref(v___x_1865_);
lean_dec(v_val_1861_);
lean_dec(v_stx_1838_);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; 
v_unused_1958_ = lean_ctor_get(v___x_1896_, 0);
lean_dec(v_unused_1958_);
v___x_1951_ = v___x_1896_;
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
else
{
lean_dec(v___x_1896_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = l_Lean_MessageData_nil;
if (v_isShared_1952_ == 0)
{
lean_ctor_set_tag(v___x_1951_, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_dec(v___x_1873_);
lean_dec_ref(v___x_1865_);
lean_dec(v_val_1861_);
lean_dec(v_stx_1838_);
v___x_1961_ = l_Lean_MessageData_nil;
if (v_isShared_1864_ == 0)
{
lean_ctor_set_tag(v___x_1863_, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1961_);
v___x_1963_ = v___x_1863_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
lean_dec(v___x_1860_);
lean_dec(v___x_1859_);
lean_dec_ref(v_env_1853_);
lean_dec(v_stx_1838_);
v___x_1966_ = l_Lean_MessageData_nil;
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
return v___x_1967_;
}
v___jp_1842_:
{
uint8_t v___x_1845_; 
v___x_1845_ = l_Lean_Exception_isInterrupt(v_a_1844_);
lean_dec_ref(v_a_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_dec_ref(v___y_1843_);
v___x_1846_ = l_Lean_MessageData_nil;
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
else
{
return v___y_1843_;
}
}
v___jp_1850_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = l_Lean_MessageData_nil;
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___boxed(lean_object* v_stx_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(v_stx_1968_, v_a_1969_, v_a_1970_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1(lean_object* v_00_u03b1_1973_, lean_object* v_x_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(v_x_1974_, v___y_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1978_, lean_object* v_x_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1(v_00_u03b1_1978_, v_x_1979_, v___y_1980_, v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec_ref(v_x_1979_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6(lean_object* v_00_u03b1_1983_, lean_object* v_ref_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(v_ref_1984_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1989_, lean_object* v_ref_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6(v_00_u03b1_1989_, v_ref_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7(lean_object* v_00_u03b1_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg();
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7(v_00_u03b1_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0(lean_object* v_00_u03b1_2005_, lean_object* v_x_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(v_x_2006_, v___y_2007_, v___y_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___boxed(lean_object* v_00_u03b1_2011_, lean_object* v_x_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0(v_00_u03b1_2011_, v_x_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3(lean_object* v_as_2017_, lean_object* v_as_x27_2018_, lean_object* v_b_2019_, lean_object* v_a_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(v_as_x27_2018_, v_b_2019_, v___y_2021_, v___y_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___boxed(lean_object* v_as_2025_, lean_object* v_as_x27_2026_, lean_object* v_b_2027_, lean_object* v_a_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3(v_as_2025_, v_as_x27_2026_, v_b_2027_, v_a_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v_as_x27_2026_);
lean_dec(v_as_2025_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5(lean_object* v_00_u03b1_2033_, lean_object* v_ref_2034_, lean_object* v_msg_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(v_ref_2034_, v_msg_2035_, v___y_2036_, v___y_2037_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2040_, lean_object* v_ref_2041_, lean_object* v_msg_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5(v_00_u03b1_2040_, v_ref_2041_, v_msg_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v_ref_2041_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2047_, lean_object* v_m_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(v_m_2048_, v_a_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2051_, lean_object* v_m_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5(v_00_u03b2_2051_, v_m_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_m_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
uint8_t v___x_2058_; 
v___x_2058_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(v_x_2056_, v_x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_){
_start:
{
uint8_t v_res_2062_; lean_object* v_r_2063_; 
v_res_2062_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6(v_00_u03b2_2059_, v_x_2060_, v_x_2061_);
lean_dec_ref(v_x_2061_);
lean_dec_ref(v_x_2060_);
v_r_2063_ = lean_box(v_res_2062_);
return v_r_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_2064_, lean_object* v_a_2065_, lean_object* v_x_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(v_a_2065_, v_x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2068_, lean_object* v_a_2069_, lean_object* v_x_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9(v_00_u03b2_2068_, v_a_2069_, v_x_2070_);
lean_dec(v_x_2070_);
lean_dec(v_a_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_2072_, lean_object* v_x_2073_, size_t v_x_2074_, lean_object* v_x_2075_){
_start:
{
uint8_t v___x_2076_; 
v___x_2076_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(v_x_2073_, v_x_2074_, v_x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2077_, lean_object* v_x_2078_, lean_object* v_x_2079_, lean_object* v_x_2080_){
_start:
{
size_t v_x_11467__boxed_2081_; uint8_t v_res_2082_; lean_object* v_r_2083_; 
v_x_11467__boxed_2081_ = lean_unbox_usize(v_x_2079_);
lean_dec(v_x_2079_);
v_res_2082_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10(v_00_u03b2_2077_, v_x_2078_, v_x_11467__boxed_2081_, v_x_2080_);
lean_dec_ref(v_x_2080_);
lean_dec_ref(v_x_2078_);
v_r_2083_ = lean_box(v_res_2082_);
return v_r_2083_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13(lean_object* v_00_u03b2_2084_, lean_object* v_keys_2085_, lean_object* v_vals_2086_, lean_object* v_heq_2087_, lean_object* v_i_2088_, lean_object* v_k_2089_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(v_keys_2085_, v_i_2088_, v_k_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___boxed(lean_object* v_00_u03b2_2091_, lean_object* v_keys_2092_, lean_object* v_vals_2093_, lean_object* v_heq_2094_, lean_object* v_i_2095_, lean_object* v_k_2096_){
_start:
{
uint8_t v_res_2097_; lean_object* v_r_2098_; 
v_res_2097_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13(v_00_u03b2_2091_, v_keys_2092_, v_vals_2093_, v_heq_2094_, v_i_2095_, v_k_2096_);
lean_dec_ref(v_k_2096_);
lean_dec_ref(v_vals_2093_);
lean_dec_ref(v_keys_2092_);
v_r_2098_ = lean_box(v_res_2097_);
return v_r_2098_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__0));
v___x_2101_ = l_Lean_stringToMessageData(v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix(lean_object* v_entry_2102_){
_start:
{
lean_object* v_text_x3f_2103_; 
v_text_x3f_2103_ = lean_ctor_get(v_entry_2102_, 1);
lean_inc(v_text_x3f_2103_);
lean_dec_ref(v_entry_2102_);
if (lean_obj_tag(v_text_x3f_2103_) == 0)
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9);
return v___x_2104_;
}
else
{
lean_object* v_val_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_val_2105_ = lean_ctor_get(v_text_x3f_2103_, 0);
lean_inc(v_val_2105_);
lean_dec_ref_known(v_text_x3f_2103_, 1);
v___x_2106_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1, &l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1_once, _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1);
v___x_2107_ = l_Lean_stringToMessageData(v_val_2105_);
v___x_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2106_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(lean_object* v_o_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_env_2114_; lean_object* v___x_2115_; lean_object* v_toEnvExtension_2116_; lean_object* v_asyncMode_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; lean_object* v___x_2120_; lean_object* v_merged_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2129_; 
v___x_2112_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2113_ = lean_st_ref_get(v___y_2110_);
v_env_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc_ref(v_env_2114_);
lean_dec(v___x_2113_);
v___x_2115_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2116_ = lean_ctor_get(v___x_2115_, 0);
v_asyncMode_2117_ = lean_ctor_get(v_toEnvExtension_2116_, 2);
v___x_2118_ = lean_box(0);
v___x_2119_ = 0;
v___x_2120_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2112_, v___x_2115_, v_env_2114_, v_asyncMode_2117_, v___x_2118_, v___x_2119_);
v_merged_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; 
v_unused_2130_ = lean_ctor_get(v___x_2120_, 1);
lean_dec(v_unused_2130_);
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_merged_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 1, v_merged_2121_);
lean_ctor_set(v___x_2123_, 0, v_o_2109_);
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_o_2109_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_merged_2121_);
v___x_2126_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg___boxed(lean_object* v_o_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(v_o_2131_, v___y_2132_);
lean_dec(v___y_2132_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2135_);
v___x_2139_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(v___x_2138_, v___y_2136_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0___boxed(lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2143_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4(lean_object* v_opts_2144_, lean_object* v_opt_2145_){
_start:
{
lean_object* v_name_2146_; lean_object* v_defValue_2147_; lean_object* v_map_2148_; lean_object* v___x_2149_; 
v_name_2146_ = lean_ctor_get(v_opt_2145_, 0);
v_defValue_2147_ = lean_ctor_get(v_opt_2145_, 1);
v_map_2148_ = lean_ctor_get(v_opts_2144_, 0);
v___x_2149_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2148_, v_name_2146_);
if (lean_obj_tag(v___x_2149_) == 0)
{
uint8_t v___x_2150_; 
v___x_2150_ = lean_unbox(v_defValue_2147_);
return v___x_2150_;
}
else
{
lean_object* v_val_2151_; 
v_val_2151_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_val_2151_);
lean_dec_ref_known(v___x_2149_, 1);
if (lean_obj_tag(v_val_2151_) == 1)
{
uint8_t v_v_2152_; 
v_v_2152_ = lean_ctor_get_uint8(v_val_2151_, 0);
lean_dec_ref_known(v_val_2151_, 0);
return v_v_2152_;
}
else
{
uint8_t v___x_2153_; 
lean_dec(v_val_2151_);
v___x_2153_ = lean_unbox(v_defValue_2147_);
return v___x_2153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_2154_, lean_object* v_opt_2155_){
_start:
{
uint8_t v_res_2156_; lean_object* v_r_2157_; 
v_res_2156_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4(v_opts_2154_, v_opt_2155_);
lean_dec_ref(v_opt_2155_);
lean_dec_ref(v_opts_2154_);
v_r_2157_ = lean_box(v_res_2156_);
return v_r_2157_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_2164_, lean_object* v_x_2165_){
_start:
{
if (lean_obj_tag(v_x_2165_) == 1)
{
lean_object* v_pre_2166_; 
v_pre_2166_ = lean_ctor_get(v_x_2165_, 0);
switch(lean_obj_tag(v_pre_2166_))
{
case 1:
{
lean_object* v_pre_2167_; 
v_pre_2167_ = lean_ctor_get(v_pre_2166_, 0);
switch(lean_obj_tag(v_pre_2167_))
{
case 0:
{
lean_object* v_str_2168_; lean_object* v_str_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_str_2168_ = lean_ctor_get(v_x_2165_, 1);
v_str_2169_ = lean_ctor_get(v_pre_2166_, 1);
v___x_2170_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_));
v___x_2171_ = lean_string_dec_eq(v_str_2169_, v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__0));
v___x_2173_ = lean_string_dec_eq(v_str_2169_, v___x_2172_);
if (v___x_2173_ == 0)
{
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__1));
v___x_2175_ = lean_string_dec_eq(v_str_2168_, v___x_2174_);
if (v___x_2175_ == 0)
{
return v___x_2175_;
}
else
{
return v_suppressElabErrors_2164_;
}
}
}
else
{
lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__2));
v___x_2177_ = lean_string_dec_eq(v_str_2168_, v___x_2176_);
if (v___x_2177_ == 0)
{
return v___x_2177_;
}
else
{
return v_suppressElabErrors_2164_;
}
}
}
case 1:
{
lean_object* v_pre_2178_; 
v_pre_2178_ = lean_ctor_get(v_pre_2167_, 0);
if (lean_obj_tag(v_pre_2178_) == 0)
{
lean_object* v_str_2179_; lean_object* v_str_2180_; lean_object* v_str_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v_str_2179_ = lean_ctor_get(v_x_2165_, 1);
v_str_2180_ = lean_ctor_get(v_pre_2166_, 1);
v_str_2181_ = lean_ctor_get(v_pre_2167_, 1);
v___x_2182_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__3));
v___x_2183_ = lean_string_dec_eq(v_str_2181_, v___x_2182_);
if (v___x_2183_ == 0)
{
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__4));
v___x_2185_ = lean_string_dec_eq(v_str_2180_, v___x_2184_);
if (v___x_2185_ == 0)
{
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__5));
v___x_2187_ = lean_string_dec_eq(v_str_2179_, v___x_2186_);
if (v___x_2187_ == 0)
{
return v___x_2187_;
}
else
{
return v_suppressElabErrors_2164_;
}
}
}
}
else
{
uint8_t v___x_2188_; 
v___x_2188_ = 0;
return v___x_2188_;
}
}
default: 
{
uint8_t v___x_2189_; 
v___x_2189_ = 0;
return v___x_2189_;
}
}
}
case 0:
{
lean_object* v_str_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_str_2190_ = lean_ctor_get(v_x_2165_, 1);
v___x_2191_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__0));
v___x_2192_ = lean_string_dec_eq(v_str_2190_, v___x_2191_);
if (v___x_2192_ == 0)
{
return v___x_2192_;
}
else
{
return v_suppressElabErrors_2164_;
}
}
default: 
{
uint8_t v___x_2193_; 
v___x_2193_ = 0;
return v___x_2193_;
}
}
}
else
{
uint8_t v___x_2194_; 
v___x_2194_ = 0;
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_2195_, lean_object* v_x_2196_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2197_; uint8_t v_res_2198_; lean_object* v_r_2199_; 
v_suppressElabErrors_boxed_2197_ = lean_unbox(v_suppressElabErrors_2195_);
v_res_2198_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_2197_, v_x_2196_);
lean_dec(v_x_2196_);
v_r_2199_ = lean_box(v_res_2198_);
return v_r_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3(lean_object* v_ref_2200_, lean_object* v_msgData_2201_, uint8_t v_severity_2202_, uint8_t v_isSilent_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; uint8_t v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v_toCold_2215_; lean_object* v___y_2216_; lean_object* v___y_2245_; lean_object* v___y_2246_; uint8_t v___y_2247_; uint8_t v___y_2248_; lean_object* v___y_2249_; uint8_t v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2272_; uint8_t v___y_2273_; lean_object* v___y_2274_; uint8_t v___y_2275_; uint8_t v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; uint8_t v___y_2282_; uint8_t v___y_2283_; uint8_t v___x_2293_; uint8_t v___y_2295_; uint8_t v___x_2301_; 
v___x_2293_ = 2;
v___x_2301_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2202_, v___x_2293_);
if (v___x_2301_ == 0)
{
v___y_2295_ = v___x_2301_;
goto v___jp_2294_;
}
else
{
uint8_t v___x_2302_; 
lean_inc_ref(v_msgData_2201_);
v___x_2302_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2201_);
if (v___x_2302_ == 0)
{
v___y_2295_ = v___x_2302_;
goto v___jp_2294_;
}
else
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec_ref(v_msgData_2201_);
v___x_2303_ = lean_box(0);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
}
v___jp_2207_:
{
lean_object* v_currNamespace_2217_; lean_object* v_openDecls_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v_env_2223_; lean_object* v_nextMacroScope_2224_; lean_object* v_ngen_2225_; lean_object* v_auxDeclNGen_2226_; lean_object* v_traceState_2227_; lean_object* v_cache_2228_; lean_object* v_recordedDeps_2229_; lean_object* v_messages_2230_; lean_object* v_infoState_2231_; lean_object* v_snapshotTasks_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2243_; 
v_currNamespace_2217_ = lean_ctor_get(v_toCold_2215_, 4);
v_openDecls_2218_ = lean_ctor_get(v_toCold_2215_, 5);
lean_inc(v_openDecls_2218_);
lean_inc(v_currNamespace_2217_);
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v_currNamespace_2217_);
lean_ctor_set(v___x_2219_, 1, v_openDecls_2218_);
v___x_2220_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v___y_2210_);
lean_inc_ref(v___y_2209_);
lean_inc_ref(v___y_2214_);
v___x_2221_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2221_, 0, v___y_2214_);
lean_ctor_set(v___x_2221_, 1, v___y_2213_);
lean_ctor_set(v___x_2221_, 2, v___y_2212_);
lean_ctor_set(v___x_2221_, 3, v___y_2209_);
lean_ctor_set(v___x_2221_, 4, v___x_2220_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*5, v___y_2208_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*5 + 1, v___y_2211_);
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*5 + 2, v_isSilent_2203_);
v___x_2222_ = lean_st_ref_take(v___y_2216_);
v_env_2223_ = lean_ctor_get(v___x_2222_, 0);
v_nextMacroScope_2224_ = lean_ctor_get(v___x_2222_, 1);
v_ngen_2225_ = lean_ctor_get(v___x_2222_, 2);
v_auxDeclNGen_2226_ = lean_ctor_get(v___x_2222_, 3);
v_traceState_2227_ = lean_ctor_get(v___x_2222_, 4);
v_cache_2228_ = lean_ctor_get(v___x_2222_, 5);
v_recordedDeps_2229_ = lean_ctor_get(v___x_2222_, 6);
v_messages_2230_ = lean_ctor_get(v___x_2222_, 7);
v_infoState_2231_ = lean_ctor_get(v___x_2222_, 8);
v_snapshotTasks_2232_ = lean_ctor_get(v___x_2222_, 9);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2234_ = v___x_2222_;
v_isShared_2235_ = v_isSharedCheck_2243_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_snapshotTasks_2232_);
lean_inc(v_infoState_2231_);
lean_inc(v_messages_2230_);
lean_inc(v_recordedDeps_2229_);
lean_inc(v_cache_2228_);
lean_inc(v_traceState_2227_);
lean_inc(v_auxDeclNGen_2226_);
lean_inc(v_ngen_2225_);
lean_inc(v_nextMacroScope_2224_);
lean_inc(v_env_2223_);
lean_dec(v___x_2222_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2243_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2236_ = lean_box(0);
v___x_2237_ = l_Lean_MessageLog_add(v___x_2221_, v_messages_2230_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 7, v___x_2237_);
v___x_2239_ = v___x_2234_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_env_2223_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_nextMacroScope_2224_);
lean_ctor_set(v_reuseFailAlloc_2242_, 2, v_ngen_2225_);
lean_ctor_set(v_reuseFailAlloc_2242_, 3, v_auxDeclNGen_2226_);
lean_ctor_set(v_reuseFailAlloc_2242_, 4, v_traceState_2227_);
lean_ctor_set(v_reuseFailAlloc_2242_, 5, v_cache_2228_);
lean_ctor_set(v_reuseFailAlloc_2242_, 6, v_recordedDeps_2229_);
lean_ctor_set(v_reuseFailAlloc_2242_, 7, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2242_, 8, v_infoState_2231_);
lean_ctor_set(v_reuseFailAlloc_2242_, 9, v_snapshotTasks_2232_);
v___x_2239_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_st_ref_put(v___y_2216_, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2236_);
return v___x_2241_;
}
}
}
v___jp_2244_:
{
lean_object* v_fileName_2253_; lean_object* v_fileMap_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2270_; 
v_fileName_2253_ = lean_ctor_get(v___y_2249_, 0);
v_fileMap_2254_ = lean_ctor_get(v___y_2249_, 1);
v___x_2255_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2201_);
v___x_2256_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(v___x_2255_, v___y_2204_, v___y_2205_);
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2270_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2270_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_inc_ref_n(v_fileMap_2254_, 2);
v___x_2261_ = l_Lean_FileMap_toPosition(v_fileMap_2254_, v___y_2251_);
lean_dec(v___y_2251_);
v___x_2262_ = l_Lean_FileMap_toPosition(v_fileMap_2254_, v___y_2252_);
lean_dec(v___y_2252_);
v___x_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1));
if (v___y_2250_ == 0)
{
lean_del_object(v___x_2259_);
lean_dec_ref(v___y_2246_);
v___y_2208_ = v___y_2247_;
v___y_2209_ = v___x_2264_;
v___y_2210_ = v_a_2257_;
v___y_2211_ = v___y_2248_;
v___y_2212_ = v___x_2263_;
v___y_2213_ = v___x_2261_;
v___y_2214_ = v_fileName_2253_;
v_toCold_2215_ = v___y_2245_;
v___y_2216_ = v___y_2205_;
goto v___jp_2207_;
}
else
{
uint8_t v___x_2265_; 
lean_inc(v_a_2257_);
v___x_2265_ = l_Lean_MessageData_hasTag(v___y_2246_, v_a_2257_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_dec_ref_known(v___x_2263_, 1);
lean_dec_ref(v___x_2261_);
lean_dec(v_a_2257_);
v___x_2266_ = lean_box(0);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2266_);
v___x_2268_ = v___x_2259_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
else
{
lean_del_object(v___x_2259_);
v___y_2208_ = v___y_2247_;
v___y_2209_ = v___x_2264_;
v___y_2210_ = v_a_2257_;
v___y_2211_ = v___y_2248_;
v___y_2212_ = v___x_2263_;
v___y_2213_ = v___x_2261_;
v___y_2214_ = v_fileName_2253_;
v_toCold_2215_ = v___y_2245_;
v___y_2216_ = v___y_2205_;
goto v___jp_2207_;
}
}
}
}
v___jp_2271_:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Syntax_getTailPos_x3f(v___y_2277_, v___y_2275_);
lean_dec(v___y_2277_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_inc(v___y_2278_);
v___y_2245_ = v___y_2272_;
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___y_2275_;
v___y_2248_ = v___y_2276_;
v___y_2249_ = v___y_2272_;
v___y_2250_ = v___y_2273_;
v___y_2251_ = v___y_2278_;
v___y_2252_ = v___y_2278_;
goto v___jp_2244_;
}
else
{
lean_object* v_val_2280_; 
v_val_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_val_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___y_2245_ = v___y_2272_;
v___y_2246_ = v___y_2274_;
v___y_2247_ = v___y_2275_;
v___y_2248_ = v___y_2276_;
v___y_2249_ = v___y_2272_;
v___y_2250_ = v___y_2273_;
v___y_2251_ = v___y_2278_;
v___y_2252_ = v_val_2280_;
goto v___jp_2244_;
}
}
v___jp_2281_:
{
lean_object* v_toCold_2284_; lean_object* v_ref_2285_; uint8_t v_suppressElabErrors_2286_; lean_object* v___x_2287_; lean_object* v___f_2288_; lean_object* v_ref_2289_; lean_object* v___x_2290_; 
v_toCold_2284_ = lean_ctor_get(v___y_2204_, 0);
v_ref_2285_ = lean_ctor_get(v___y_2204_, 2);
v_suppressElabErrors_2286_ = lean_ctor_get_uint8(v___y_2204_, sizeof(void*)*3 + 2);
v___x_2287_ = lean_box(v_suppressElabErrors_2286_);
v___f_2288_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2288_, 0, v___x_2287_);
v_ref_2289_ = l_Lean_replaceRef(v_ref_2200_, v_ref_2285_);
v___x_2290_ = l_Lean_Syntax_getPos_x3f(v_ref_2289_, v___y_2282_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_unsigned_to_nat(0u);
v___y_2272_ = v_toCold_2284_;
v___y_2273_ = v_suppressElabErrors_2286_;
v___y_2274_ = v___f_2288_;
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v_ref_2289_;
v___y_2278_ = v___x_2291_;
goto v___jp_2271_;
}
else
{
lean_object* v_val_2292_; 
v_val_2292_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_val_2292_);
lean_dec_ref_known(v___x_2290_, 1);
v___y_2272_ = v_toCold_2284_;
v___y_2273_ = v_suppressElabErrors_2286_;
v___y_2274_ = v___f_2288_;
v___y_2275_ = v___y_2282_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v_ref_2289_;
v___y_2278_ = v_val_2292_;
goto v___jp_2271_;
}
}
v___jp_2294_:
{
uint8_t v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = 1;
v___x_2297_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2202_, v___x_2296_);
if (v___x_2297_ == 0)
{
v___y_2282_ = v___y_2295_;
v___y_2283_ = v_severity_2202_;
goto v___jp_2281_;
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2298_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2204_);
v___x_2299_ = l_Lean_warningAsError;
v___x_2300_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4(v___x_2298_, v___x_2299_);
lean_dec_ref(v___x_2298_);
if (v___x_2300_ == 0)
{
v___y_2282_ = v___y_2295_;
v___y_2283_ = v_severity_2202_;
goto v___jp_2281_;
}
else
{
v___y_2282_ = v___y_2295_;
v___y_2283_ = v___x_2293_;
goto v___jp_2281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_2305_, lean_object* v_msgData_2306_, lean_object* v_severity_2307_, lean_object* v_isSilent_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
uint8_t v_severity_boxed_2312_; uint8_t v_isSilent_boxed_2313_; lean_object* v_res_2314_; 
v_severity_boxed_2312_ = lean_unbox(v_severity_2307_);
v_isSilent_boxed_2313_ = lean_unbox(v_isSilent_2308_);
v_res_2314_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3(v_ref_2305_, v_msgData_2306_, v_severity_boxed_2312_, v_isSilent_boxed_2313_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v_ref_2305_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2(lean_object* v_ref_2315_, lean_object* v_msgData_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
uint8_t v___x_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = 1;
v___x_2321_ = 0;
v___x_2322_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3(v_ref_2315_, v_msgData_2316_, v___x_2320_, v___x_2321_, v___y_2317_, v___y_2318_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2___boxed(lean_object* v_ref_2323_, lean_object* v_msgData_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2(v_ref_2323_, v_msgData_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v_ref_2323_);
return v_res_2328_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__0));
v___x_2331_ = l_Lean_stringToMessageData(v___x_2330_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__2));
v___x_2334_ = l_Lean_stringToMessageData(v___x_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(lean_object* v_linterOption_2335_, lean_object* v_stx_2336_, lean_object* v_msg_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_name_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2359_; 
v_name_2341_ = lean_ctor_get(v_linterOption_2335_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_linterOption_2335_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; 
v_unused_2360_ = lean_ctor_get(v_linterOption_2335_, 1);
lean_dec(v_unused_2360_);
v___x_2343_ = v_linterOption_2335_;
v_isShared_2344_ = v_isSharedCheck_2359_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_name_2341_);
lean_dec(v_linterOption_2335_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2359_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2345_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1);
lean_inc(v_name_2341_);
v___x_2346_ = l_Lean_MessageData_ofName(v_name_2341_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 7);
lean_ctor_set(v___x_2343_, 1, v___x_2346_);
lean_ctor_set(v___x_2343_, 0, v___x_2345_);
v___x_2348_ = v___x_2343_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_disable_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2349_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v_disable_2351_ = l_Lean_MessageData_note(v___x_2350_);
v___x_2352_ = l_Lean_Linter_linterMessageTag;
v___x_2353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2353_, 0, v_msg_2337_);
lean_ctor_set(v___x_2353_, 1, v_disable_2351_);
v___x_2354_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2355_, 0, v_name_2341_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
lean_inc(v_stx_2336_);
v___x_2356_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2356_, 0, v_stx_2336_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2(v_stx_2336_, v___x_2356_, v___y_2338_, v___y_2339_);
lean_dec(v_stx_2336_);
return v___x_2357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___boxed(lean_object* v_linterOption_2361_, lean_object* v_stx_2362_, lean_object* v_msg_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v_linterOption_2361_, v_stx_2362_, v_msg_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2367_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__1(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__0));
v___x_2370_ = l_Lean_stringToMessageData(v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__3(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__2));
v___x_2373_ = l_Lean_stringToMessageData(v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__5(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__4));
v___x_2376_ = l_Lean_stringToMessageData(v___x_2375_);
return v___x_2376_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__7(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__6));
v___x_2379_ = l_Lean_stringToMessageData(v___x_2378_);
return v___x_2379_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__8));
v___x_2382_ = l_Lean_stringToMessageData(v___x_2381_);
return v___x_2382_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__11(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__10));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__13(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__12));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__15(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__14));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax(lean_object* v_stx_2392_, lean_object* v_macroStack_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v_env_2399_; lean_object* v___x_2400_; lean_object* v_toEnvExtension_2401_; lean_object* v_asyncMode_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2397_ = lean_box(1);
v___x_2398_ = lean_st_ref_get(v_a_2395_);
v_env_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc_ref(v_env_2399_);
lean_dec(v___x_2398_);
v___x_2400_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_2401_ = lean_ctor_get(v___x_2400_, 0);
v_asyncMode_2402_ = lean_ctor_get(v_toEnvExtension_2401_, 2);
lean_inc(v_stx_2392_);
v___x_2403_ = l_Lean_Syntax_getKind(v_stx_2392_);
v___x_2404_ = lean_box(0);
v___x_2405_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2397_, v___x_2400_, v_env_2399_, v_asyncMode_2402_, v___x_2404_);
v___x_2406_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2405_, v___x_2403_);
lean_dec(v___x_2405_);
if (lean_obj_tag(v___x_2406_) == 1)
{
lean_object* v_val_2407_; lean_object* v___x_2408_; lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2552_; 
v_val_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_val_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2408_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(v_a_2394_, v_a_2395_);
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2552_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2552_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; uint8_t v___x_2414_; 
v___x_2413_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_2414_ = l_Lean_Linter_getLinterValue(v___x_2413_, v_a_2409_);
lean_dec(v_a_2409_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
lean_dec(v_val_2407_);
lean_dec(v___x_2403_);
lean_dec(v_macroStack_2393_);
lean_dec(v_stx_2392_);
v___x_2415_ = lean_box(0);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2415_);
v___x_2417_ = v___x_2411_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
else
{
lean_object* v___x_2419_; 
lean_del_object(v___x_2411_);
v___x_2419_ = l_Lean_Core_shouldCheckDeprecated___redArg(v_stx_2392_, v_a_2394_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2543_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2543_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2543_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
uint8_t v___x_2424_; 
v___x_2424_ = lean_unbox(v_a_2420_);
lean_dec(v_a_2420_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
lean_dec(v_val_2407_);
lean_dec(v___x_2403_);
lean_dec(v_macroStack_2393_);
lean_dec(v_stx_2392_);
v___x_2425_ = lean_box(0);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2425_);
v___x_2427_ = v___x_2422_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_del_object(v___x_2422_);
v___x_2429_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix(v_val_2407_);
v___x_2430_ = l_Lean_Syntax_getHeadInfo(v_stx_2392_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v___x_2431_; 
lean_dec_ref_known(v___x_2430_, 4);
lean_dec(v_macroStack_2393_);
lean_inc(v_stx_2392_);
v___x_2431_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(v_stx_2392_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___x_2431_, 1);
v___x_2433_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__1);
v___x_2434_ = l_Lean_MessageData_ofName(v___x_2403_);
v___x_2435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__3);
v___x_2437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v___x_2429_);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v_a_2432_);
v___x_2440_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2413_, v_stx_2392_, v___x_2439_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2448_; 
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2448_ == 0)
{
lean_object* v_unused_2449_; 
v_unused_2449_ = lean_ctor_get(v___x_2440_, 0);
lean_dec(v_unused_2449_);
v___x_2442_ = v___x_2440_;
v_isShared_2443_ = v_isSharedCheck_2448_;
goto v_resetjp_2441_;
}
else
{
lean_dec(v___x_2440_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2448_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2444_ = lean_box(0);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v___x_2444_);
v___x_2446_ = v___x_2442_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
else
{
return v___x_2440_;
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v___x_2429_);
lean_dec(v___x_2403_);
lean_dec(v_stx_2392_);
v_a_2450_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2431_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2431_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_dec(v___x_2430_);
if (lean_obj_tag(v_macroStack_2393_) == 0)
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2458_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__1);
v___x_2459_ = l_Lean_MessageData_ofName(v___x_2403_);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__3);
v___x_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
lean_ctor_set(v___x_2463_, 1, v___x_2429_);
v___x_2464_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2413_, v_stx_2392_, v___x_2463_, v_a_2394_, v_a_2395_);
return v___x_2464_;
}
else
{
lean_object* v_head_2465_; lean_object* v_tail_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_stx_2392_);
v_head_2465_ = lean_ctor_get(v_macroStack_2393_, 0);
v_tail_2466_ = lean_ctor_get(v_macroStack_2393_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v_macroStack_2393_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2468_ = v_macroStack_2393_;
v_isShared_2469_ = v_isSharedCheck_2542_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_tail_2466_);
lean_inc(v_head_2465_);
lean_dec(v_macroStack_2393_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2542_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
if (lean_obj_tag(v_tail_2466_) == 0)
{
lean_object* v_before_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2490_; 
v_before_2470_ = lean_ctor_get(v_head_2465_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_head_2465_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v_head_2465_, 1);
lean_dec(v_unused_2491_);
v___x_2472_ = v_head_2465_;
v_isShared_2473_ = v_isSharedCheck_2490_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_before_2470_);
lean_dec(v_head_2465_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2490_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2474_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__5, &l_Lean_Elab_checkDeprecatedSyntax___closed__5_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__5);
lean_inc(v_before_2470_);
v___x_2475_ = l_Lean_Syntax_getKind(v_before_2470_);
v___x_2476_ = l_Lean_MessageData_ofName(v___x_2475_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set_tag(v___x_2472_, 7);
lean_ctor_set(v___x_2472_, 1, v___x_2476_);
lean_ctor_set(v___x_2472_, 0, v___x_2474_);
v___x_2478_ = v___x_2472_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__7, &l_Lean_Elab_checkDeprecatedSyntax___closed__7_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__7);
if (v_isShared_2469_ == 0)
{
lean_ctor_set_tag(v___x_2468_, 7);
lean_ctor_set(v___x_2468_, 1, v___x_2479_);
lean_ctor_set(v___x_2468_, 0, v___x_2478_);
v___x_2481_ = v___x_2468_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2482_ = l_Lean_MessageData_ofName(v___x_2403_);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9);
v___x_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
lean_ctor_set(v___x_2486_, 1, v___x_2429_);
v___x_2487_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2413_, v_before_2470_, v___x_2486_, v_a_2394_, v_a_2395_);
return v___x_2487_;
}
}
}
}
else
{
lean_object* v_head_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2540_; 
v_head_2492_ = lean_ctor_get(v_tail_2466_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v_tail_2466_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; 
v_unused_2541_ = lean_ctor_get(v_tail_2466_, 1);
lean_dec(v_unused_2541_);
v___x_2494_ = v_tail_2466_;
v_isShared_2495_ = v_isSharedCheck_2540_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_head_2492_);
lean_dec(v_tail_2466_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2540_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_before_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2538_; 
v_before_2496_ = lean_ctor_get(v_head_2465_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_head_2465_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; 
v_unused_2539_ = lean_ctor_get(v_head_2465_, 1);
lean_dec(v_unused_2539_);
v___x_2498_ = v_head_2465_;
v_isShared_2499_ = v_isSharedCheck_2538_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_before_2496_);
lean_dec(v_head_2465_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2538_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_before_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2536_; 
v_before_2500_ = lean_ctor_get(v_head_2492_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_head_2492_);
if (v_isSharedCheck_2536_ == 0)
{
lean_object* v_unused_2537_; 
v_unused_2537_ = lean_ctor_get(v_head_2492_, 1);
lean_dec(v_unused_2537_);
v___x_2502_ = v_head_2492_;
v_isShared_2503_ = v_isSharedCheck_2536_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_before_2500_);
lean_dec(v_head_2492_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2536_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___y_2507_; uint8_t v___x_2529_; 
v___x_2504_ = l_Lean_Syntax_getKind(v_before_2500_);
lean_inc(v_before_2496_);
v___x_2505_ = l_Lean_Syntax_getKind(v_before_2496_);
v___x_2529_ = lean_name_eq(v___x_2504_, v___x_2505_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2530_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__13, &l_Lean_Elab_checkDeprecatedSyntax___closed__13_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__13);
v___x_2531_ = l_Lean_MessageData_ofName(v___x_2504_);
v___x_2532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__15, &l_Lean_Elab_checkDeprecatedSyntax___closed__15_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__15);
v___x_2534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2532_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___y_2507_ = v___x_2534_;
goto v___jp_2506_;
}
else
{
lean_object* v___x_2535_; 
lean_dec(v___x_2504_);
v___x_2535_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9);
v___y_2507_ = v___x_2535_;
goto v___jp_2506_;
}
v___jp_2506_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2508_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__5, &l_Lean_Elab_checkDeprecatedSyntax___closed__5_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__5);
v___x_2509_ = l_Lean_MessageData_ofName(v___x_2505_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set_tag(v___x_2502_, 7);
lean_ctor_set(v___x_2502_, 1, v___x_2509_);
lean_ctor_set(v___x_2502_, 0, v___x_2508_);
v___x_2511_ = v___x_2502_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2512_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9);
if (v_isShared_2495_ == 0)
{
lean_ctor_set_tag(v___x_2494_, 7);
lean_ctor_set(v___x_2494_, 1, v___x_2512_);
lean_ctor_set(v___x_2494_, 0, v___x_2511_);
v___x_2514_ = v___x_2494_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2499_ == 0)
{
lean_ctor_set_tag(v___x_2498_, 7);
lean_ctor_set(v___x_2498_, 1, v___y_2507_);
lean_ctor_set(v___x_2498_, 0, v___x_2514_);
v___x_2516_ = v___x_2498_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v___y_2507_);
v___x_2516_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__11, &l_Lean_Elab_checkDeprecatedSyntax___closed__11_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__11);
if (v_isShared_2469_ == 0)
{
lean_ctor_set_tag(v___x_2468_, 7);
lean_ctor_set(v___x_2468_, 1, v___x_2517_);
lean_ctor_set(v___x_2468_, 0, v___x_2516_);
v___x_2519_ = v___x_2468_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2520_ = l_Lean_MessageData_ofName(v___x_2403_);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___x_2512_);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
lean_ctor_set(v___x_2523_, 1, v___x_2429_);
v___x_2524_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2413_, v_before_2496_, v___x_2523_, v_a_2394_, v_a_2395_);
return v___x_2524_;
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
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_val_2407_);
lean_dec(v___x_2403_);
lean_dec(v_macroStack_2393_);
lean_dec(v_stx_2392_);
v_a_2544_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2419_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2419_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
lean_dec(v___x_2406_);
lean_dec(v___x_2403_);
lean_dec(v_macroStack_2393_);
lean_dec(v_stx_2392_);
v___x_2553_ = lean_box(0);
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___boxed(lean_object* v_stx_2555_, lean_object* v_macroStack_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Elab_checkDeprecatedSyntax(v_stx_2555_, v_macroStack_2556_, v_a_2557_, v_a_2558_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0(lean_object* v_o_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(v_o_2561_, v___y_2563_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___boxed(lean_object* v_o_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0(v_o_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
return v_res_2570_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__0));
v___x_2573_ = l_Lean_stringToMessageData(v___x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax(lean_object* v_stx_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_env_2580_; lean_object* v___x_2581_; lean_object* v_toEnvExtension_2582_; lean_object* v_asyncMode_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2578_ = lean_box(1);
v___x_2579_ = lean_st_ref_get(v_a_2576_);
v_env_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc_ref(v_env_2580_);
lean_dec(v___x_2579_);
v___x_2581_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_2582_ = lean_ctor_get(v___x_2581_, 0);
v_asyncMode_2583_ = lean_ctor_get(v_toEnvExtension_2582_, 2);
v___x_2584_ = lean_box(0);
v___x_2585_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2578_, v___x_2581_, v_env_2580_, v_asyncMode_2583_, v___x_2584_);
lean_inc(v_stx_2574_);
v___x_2586_ = l_Lean_Syntax_getKind(v_stx_2574_);
v___x_2587_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2585_, v___x_2586_);
lean_dec(v___x_2585_);
if (lean_obj_tag(v___x_2587_) == 1)
{
lean_object* v_val_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2647_; 
v_val_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2647_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_val_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2647_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_Syntax_getHeadInfo(v_stx_2574_);
if (lean_obj_tag(v___x_2592_) == 1)
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_dec_ref_known(v___x_2592_, 2);
lean_dec(v_val_2588_);
lean_dec(v___x_2586_);
lean_dec(v_stx_2574_);
v___x_2593_ = lean_box(0);
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2593_);
v___x_2595_ = v___x_2590_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
else
{
lean_object* v___x_2597_; lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2646_; 
lean_dec(v___x_2592_);
lean_del_object(v___x_2590_);
v___x_2597_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(v_a_2575_, v_a_2576_);
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2646_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2646_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_2603_ = l_Lean_Linter_getLinterValue(v___x_2602_, v_a_2598_);
lean_dec(v_a_2598_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
lean_dec(v_val_2588_);
lean_dec(v___x_2586_);
lean_dec(v_stx_2574_);
v___x_2604_ = lean_box(0);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2604_);
v___x_2606_ = v___x_2600_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
else
{
lean_object* v___x_2608_; 
lean_del_object(v___x_2600_);
v___x_2608_ = l_Lean_Core_shouldCheckDeprecated___redArg(v_stx_2574_, v_a_2575_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2637_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2637_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2637_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
uint8_t v___x_2613_; 
v___x_2613_ = lean_unbox(v_a_2609_);
lean_dec(v_a_2609_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_dec(v_val_2588_);
lean_dec(v___x_2586_);
lean_dec(v_stx_2574_);
v___x_2614_ = lean_box(0);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2614_);
v___x_2616_ = v___x_2611_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
else
{
lean_object* v___x_2618_; 
lean_del_object(v___x_2611_);
lean_inc(v_stx_2574_);
v___x_2618_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(v_stx_2574_, v_a_2575_, v_a_2576_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1, &l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1_once, _init_l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1);
v___x_2621_ = l_Lean_MessageData_ofName(v___x_2586_);
v___x_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2620_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9);
v___x_2624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix(v_val_2588_);
v___x_2626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2624_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v_a_2619_);
v___x_2628_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2602_, v_stx_2574_, v___x_2627_, v_a_2575_, v_a_2576_);
return v___x_2628_;
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_val_2588_);
lean_dec(v___x_2586_);
lean_dec(v_stx_2574_);
v_a_2629_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2618_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2618_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_val_2588_);
lean_dec(v___x_2586_);
lean_dec(v_stx_2574_);
v_a_2638_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2608_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2608_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec(v___x_2587_);
lean_dec(v___x_2586_);
lean_dec(v_stx_2574_);
v___x_2648_ = lean_box(0);
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
return v___x_2649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax___boxed(lean_object* v_stx_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_Elab_checkDeprecatedQuotedSyntax(v_stx_2650_, v_a_2651_, v_a_2652_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
return v_res_2654_;
}
}
lean_object* runtime_initialize_Lean_MonadEnv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Hint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_DeprecatedSyntax_FormatReplacement(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeprecatedSyntax_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeprecatedSyntax_FormatReplacement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_3204438947____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_deprecated_syntax = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_deprecated_syntax);
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_deprecatedSyntaxExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_deprecatedSyntaxExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_Basic_1994602318____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_deprecatedSyntaxReplacementExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_deprecatedSyntaxReplacementExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DeprecatedSyntax_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_MonadEnv(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Elab_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Hint(uint8_t builtin);
lean_object* initialize_Lean_Elab_DeprecatedSyntax_FormatReplacement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeprecatedSyntax_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeprecatedSyntax_FormatReplacement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeprecatedSyntax_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DeprecatedSyntax_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DeprecatedSyntax_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
