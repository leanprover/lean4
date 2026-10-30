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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_518_ = lean_nat_add(v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec(v___y_516_);
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
lean_ctor_set(v___x_522_, 3, v___y_515_);
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
lean_ctor_set(v_reuseFailAlloc_526_, 3, v___y_515_);
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
v___y_515_ = v___x_539_;
v___y_516_ = v___x_540_;
v___y_517_ = v_size_541_;
goto v___jp_514_;
}
else
{
lean_object* v___x_542_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___y_515_ = v___x_539_;
v___y_516_ = v___x_540_;
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
v___x_676_ = lean_nat_add(v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec(v___y_674_);
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
lean_ctor_set(v___x_656_, 3, v___y_673_);
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
lean_ctor_set(v_reuseFailAlloc_681_, 3, v___y_673_);
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
v___y_673_ = v___x_688_;
v___y_674_ = v___x_689_;
v___y_675_ = v_size_690_;
goto v___jp_672_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___y_673_ = v___x_688_;
v___y_674_ = v___x_689_;
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
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_918_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_919_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
lean_ctor_set(v___x_921_, 3, v___x_920_);
lean_ctor_set(v___x_921_, 4, v___x_919_);
lean_ctor_set(v___x_921_, 5, v___x_919_);
lean_ctor_set(v___x_921_, 6, v___x_919_);
lean_ctor_set(v___x_921_, 7, v___x_919_);
lean_ctor_set(v___x_921_, 8, v___x_919_);
lean_ctor_set(v___x_921_, 9, v___x_919_);
lean_ctor_set(v___x_921_, 10, v___x_919_);
lean_ctor_set(v___x_921_, 11, v___x_918_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_unsigned_to_nat(32u);
v___x_923_ = lean_mk_empty_array_with_capacity(v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_925_ = ((size_t)5ULL);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_unsigned_to_nat(32u);
v___x_928_ = lean_mk_empty_array_with_capacity(v___x_927_);
v___x_929_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_930_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
lean_ctor_set(v___x_930_, 2, v___x_926_);
lean_ctor_set(v___x_930_, 3, v___x_926_);
lean_ctor_set_usize(v___x_930_, 4, v___x_925_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_931_ = lean_box(1);
v___x_932_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_933_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_932_);
lean_ctor_set(v___x_934_, 2, v___x_931_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v_toCold_940_; lean_object* v_env_941_; lean_object* v_options_942_; uint8_t v___x_943_; lean_object* v_env_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_939_ = lean_st_ref_get(v___y_937_);
v_toCold_940_ = lean_ctor_get(v___y_936_, 0);
v_env_941_ = lean_ctor_get(v___x_939_, 0);
lean_inc_ref(v_env_941_);
lean_dec(v___x_939_);
v_options_942_ = lean_ctor_get(v_toCold_940_, 2);
v___x_943_ = 0;
v_env_944_ = l_Lean_Environment_setRecordingDeps(v_env_941_, v___x_943_);
v___x_945_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_946_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_942_);
v___x_947_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_947_, 0, v_env_944_);
lean_ctor_set(v___x_947_, 1, v___x_945_);
lean_ctor_set(v___x_947_, 2, v___x_946_);
lean_ctor_set(v___x_947_, 3, v_options_942_);
v___x_948_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v_msgData_935_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(v_msgData_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_ref_959_; lean_object* v___x_960_; lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_969_; 
v_ref_959_ = lean_ctor_get(v___y_956_, 2);
v___x_960_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_955_, v___y_956_, v___y_957_);
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_969_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_969_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_967_; 
lean_inc(v_ref_959_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v_ref_959_);
lean_ctor_set(v___x_965_, 1, v_a_961_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 1);
lean_ctor_set(v___x_963_, 0, v___x_965_);
v___x_967_ = v___x_963_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
if (lean_obj_tag(v_x_975_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_a_979_ = lean_ctor_get(v_x_975_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v_x_975_, 1);
v___x_980_ = l_Lean_stringToMessageData(v_a_979_);
v___x_981_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(v___x_980_, v___y_976_, v___y_977_);
return v___x_981_;
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_a_982_ = lean_ctor_get(v_x_975_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v_x_975_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v_x_975_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set_tag(v___x_984_, 0);
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg___boxed(lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(v_x_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_994_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
v___x_996_ = l_Lean_Elab_abortCommandExceptionId;
v___x_997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___closed__0);
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg___boxed(lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg();
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg(lean_object* v_typeName_1003_, lean_object* v_constName_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v_env_1009_; uint8_t v___x_1010_; 
v___x_1008_ = lean_st_ref_get(v___y_1006_);
v_env_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_ref(v_env_1009_);
lean_dec(v___x_1008_);
lean_inc(v_constName_1004_);
v___x_1010_ = lean_has_compile_error(v_env_1009_, v_constName_1004_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v_env_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1011_ = lean_st_ref_get(v___y_1006_);
v_env_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc_ref(v_env_1012_);
lean_dec(v___x_1011_);
v___x_1013_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1005_);
v___x_1014_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1012_, v___x_1013_, v_typeName_1003_, v_constName_1004_);
lean_dec_ref(v___x_1013_);
v___x_1015_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(v___x_1014_, v___y_1005_, v___y_1006_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v___x_1017_; lean_object* v_env_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec_ref_known(v___x_1016_, 1);
v___x_1017_ = lean_st_ref_get(v___y_1006_);
v_env_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc_ref(v_env_1018_);
lean_dec(v___x_1017_);
v___x_1019_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1005_);
v___x_1020_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1018_, v___x_1019_, v_typeName_1003_, v_constName_1004_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(v___x_1020_, v___y_1005_, v___y_1006_);
return v___x_1021_;
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_constName_1004_);
lean_dec(v_typeName_1003_);
v_a_1022_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1016_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1016_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg___boxed(lean_object* v_typeName_1030_, lean_object* v_constName_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg(v_typeName_1030_, v_constName_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe(lean_object* v_declName_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___closed__1));
v___x_1045_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg(v___x_1044_, v_declName_1040_, v_a_1041_, v_a_1042_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe___boxed(lean_object* v_declName_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe(v_declName_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1(lean_object* v_00_u03b1_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___redArg();
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__1(v_00_u03b1_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0(lean_object* v_00_u03b1_1061_, lean_object* v_typeName_1062_, lean_object* v_constName_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___redArg(v_typeName_1062_, v_constName_1063_, v___y_1064_, v___y_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0___boxed(lean_object* v_00_u03b1_1068_, lean_object* v_typeName_1069_, lean_object* v_constName_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0(v_00_u03b1_1068_, v_typeName_1069_, v_constName_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0(lean_object* v_00_u03b1_1075_, lean_object* v_x_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___redArg(v_x_1076_, v___y_1077_, v___y_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1081_, lean_object* v_x_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0(v_00_u03b1_1081_, v_x_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1087_, lean_object* v_msg_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_1088_, v___y_1089_, v___y_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_msg_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1(v_00_u03b1_1093_, v_msg_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0(uint8_t v___x_1099_, lean_object* v_s_1100_){
_start:
{
uint8_t v___x_1104_; 
v___x_1104_ = l_Lean_Syntax_isAtom(v_s_1100_);
if (v___x_1104_ == 0)
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Lean_Syntax_isIdent(v_s_1100_);
if (v___x_1105_ == 0)
{
return v___x_1105_;
}
else
{
goto v___jp_1101_;
}
}
else
{
goto v___jp_1101_;
}
v___jp_1101_:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_Syntax_getHeadInfo(v_s_1100_);
if (lean_obj_tag(v___x_1102_) == 0)
{
uint8_t v___x_1103_; 
lean_dec_ref_known(v___x_1102_, 4);
v___x_1103_ = 0;
return v___x_1103_;
}
else
{
lean_dec(v___x_1102_);
return v___x_1099_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0___boxed(lean_object* v___x_1106_, lean_object* v_s_1107_){
_start:
{
uint8_t v___x_10015__boxed_1108_; uint8_t v_res_1109_; lean_object* v_r_1110_; 
v___x_10015__boxed_1108_ = lean_unbox(v___x_1106_);
v_res_1109_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0(v___x_10015__boxed_1108_, v_s_1107_);
lean_dec(v_s_1107_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___x_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg(){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___closed__0);
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg___boxed(lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg();
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(lean_object* v_x_1119_, lean_object* v___y_1120_){
_start:
{
if (lean_obj_tag(v_x_1119_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; 
v_a_1121_ = lean_ctor_get(v_x_1119_, 0);
lean_inc(v_a_1121_);
v___x_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_a_1121_);
lean_ctor_set(v___x_1122_, 1, v___y_1120_);
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1124_; 
v_a_1123_ = lean_ctor_get(v_x_1119_, 0);
lean_inc(v_a_1123_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1123_);
lean_ctor_set(v___x_1124_, 1, v___y_1120_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg___boxed(lean_object* v_x_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(v_x_1125_, v___y_1126_);
lean_dec_ref(v_x_1125_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1(lean_object* v_env_1128_, lean_object* v_stx_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1128_, v_stx_1129_, v___y_1130_, v___y_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
if (lean_obj_tag(v_a_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
v_a_1134_ = lean_ctor_get(v___x_1132_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v___x_1132_, 0);
lean_dec(v_unused_1143_);
v___x_1136_ = v___x_1132_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_box(0);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_a_1134_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
lean_object* v_val_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1172_; 
v_val_1144_ = lean_ctor_get(v_a_1133_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_a_1133_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1146_ = v_a_1133_;
v_isShared_1147_ = v_isSharedCheck_1172_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_val_1144_);
lean_dec(v_a_1133_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1172_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_snd_1148_; 
v_snd_1148_ = lean_ctor_get(v_val_1144_, 1);
lean_inc(v_snd_1148_);
lean_dec(v_val_1144_);
if (lean_obj_tag(v_snd_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1158_; 
lean_del_object(v___x_1146_);
v_a_1149_ = lean_ctor_get(v___x_1132_, 1);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1132_, 2);
v_a_1150_ = lean_ctor_get(v_snd_1148_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_snd_1148_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1152_ = v_snd_1148_;
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v_snd_1148_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(v___x_1155_, v_a_1149_);
lean_dec_ref(v___x_1155_);
return v___x_1156_;
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1171_; 
v_a_1159_ = lean_ctor_get(v___x_1132_, 1);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1132_, 2);
v_a_1160_ = lean_ctor_get(v_snd_1148_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_snd_1148_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1162_ = v_snd_1148_;
v_isShared_1163_ = v_isSharedCheck_1171_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v_snd_1148_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1171_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_a_1160_);
v___x_1165_ = v___x_1146_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1165_);
v___x_1167_ = v___x_1162_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(v___x_1167_, v_a_1159_);
lean_dec_ref(v___x_1167_);
return v___x_1168_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
v_a_1173_ = lean_ctor_get(v___x_1132_, 0);
v_a_1174_ = lean_ctor_get(v___x_1132_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1132_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_inc(v_a_1173_);
lean_dec(v___x_1132_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1173_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1___boxed(lean_object* v_env_1182_, lean_object* v_stx_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1(v_env_1182_, v_stx_1183_, v___y_1184_, v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(lean_object* v_ref_1187_, lean_object* v_msg_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_toCold_1192_; lean_object* v_currRecDepth_1193_; lean_object* v_ref_1194_; uint16_t v_optionFlags_1195_; uint8_t v_suppressElabErrors_1196_; uint8_t v_checkDeprecated_1197_; uint8_t v_isRecordingDeps_1198_; lean_object* v_ref_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_toCold_1192_ = lean_ctor_get(v___y_1189_, 0);
v_currRecDepth_1193_ = lean_ctor_get(v___y_1189_, 1);
v_ref_1194_ = lean_ctor_get(v___y_1189_, 2);
v_optionFlags_1195_ = lean_ctor_get_uint16(v___y_1189_, sizeof(void*)*3);
v_suppressElabErrors_1196_ = lean_ctor_get_uint8(v___y_1189_, sizeof(void*)*3 + 2);
v_checkDeprecated_1197_ = lean_ctor_get_uint8(v___y_1189_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1198_ = lean_ctor_get_uint8(v___y_1189_, sizeof(void*)*3 + 4);
v_ref_1199_ = l_Lean_replaceRef(v_ref_1187_, v_ref_1194_);
lean_inc(v_currRecDepth_1193_);
lean_inc_ref(v_toCold_1192_);
v___x_1200_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1200_, 0, v_toCold_1192_);
lean_ctor_set(v___x_1200_, 1, v_currRecDepth_1193_);
lean_ctor_set(v___x_1200_, 2, v_ref_1199_);
lean_ctor_set_uint16(v___x_1200_, sizeof(void*)*3, v_optionFlags_1195_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*3 + 2, v_suppressElabErrors_1196_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*3 + 3, v_checkDeprecated_1197_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*3 + 4, v_isRecordingDeps_1198_);
v___x_1201_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_1188_, v___x_1200_, v___y_1190_);
lean_dec_ref_known(v___x_1200_, 3);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1202_, lean_object* v_msg_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(v_ref_1202_, v_msg_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v_ref_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4(lean_object* v_env_1208_, lean_object* v_currNamespace_1209_, lean_object* v_openDecls_1210_, lean_object* v_n_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = l_Lean_ResolveName_resolveNamespace(v_env_1208_, v_currNamespace_1209_, v_openDecls_1210_, v_n_1211_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v___y_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4___boxed(lean_object* v_env_1216_, lean_object* v_currNamespace_1217_, lean_object* v_openDecls_1218_, lean_object* v_n_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4(v_env_1216_, v_currNamespace_1217_, v_openDecls_1218_, v_n_1219_, v___y_1220_, v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3(lean_object* v_env_1223_, lean_object* v___x_1224_, lean_object* v_currNamespace_1225_, lean_object* v_openDecls_1226_, lean_object* v_n_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = l_Lean_ResolveName_resolveGlobalName(v_env_1223_, v___x_1224_, v_currNamespace_1225_, v_openDecls_1226_, v_n_1227_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v___y_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3___boxed(lean_object* v_env_1232_, lean_object* v___x_1233_, lean_object* v_currNamespace_1234_, lean_object* v_openDecls_1235_, lean_object* v_n_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3(v_env_1232_, v___x_1233_, v_currNamespace_1234_, v_openDecls_1235_, v_n_1236_, v___y_1237_, v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___x_1233_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2(lean_object* v_currNamespace_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_currNamespace_1240_);
lean_ctor_set(v___x_1243_, 1, v___y_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2(v_currNamespace_1244_, v___y_1245_, v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1247_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = l_Lean_maxRecDepthErrorMessage;
v___x_1254_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3);
v___x_1256_ = l_Lean_MessageData_ofFormat(v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4);
v___x_1258_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__2));
v___x_1259_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___x_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(lean_object* v_ref_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_ref_1260_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(v_ref_1265_);
return v_res_1267_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1268_; double v___x_1269_; 
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_float_of_nat(v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(lean_object* v_cls_1273_, lean_object* v_msg_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_ref_1278_; lean_object* v___x_1279_; lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1325_; 
v_ref_1278_ = lean_ctor_get(v___y_1275_, 2);
v___x_1279_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_1274_, v___y_1275_, v___y_1276_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1325_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1325_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v_traceState_1285_; lean_object* v_env_1286_; lean_object* v_nextMacroScope_1287_; lean_object* v_ngen_1288_; lean_object* v_auxDeclNGen_1289_; lean_object* v_cache_1290_; lean_object* v_recordedDeps_1291_; lean_object* v_messages_1292_; lean_object* v_infoState_1293_; lean_object* v_snapshotTasks_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1324_; 
v___x_1284_ = lean_st_ref_take(v___y_1276_);
v_traceState_1285_ = lean_ctor_get(v___x_1284_, 4);
v_env_1286_ = lean_ctor_get(v___x_1284_, 0);
v_nextMacroScope_1287_ = lean_ctor_get(v___x_1284_, 1);
v_ngen_1288_ = lean_ctor_get(v___x_1284_, 2);
v_auxDeclNGen_1289_ = lean_ctor_get(v___x_1284_, 3);
v_cache_1290_ = lean_ctor_get(v___x_1284_, 5);
v_recordedDeps_1291_ = lean_ctor_get(v___x_1284_, 6);
v_messages_1292_ = lean_ctor_get(v___x_1284_, 7);
v_infoState_1293_ = lean_ctor_get(v___x_1284_, 8);
v_snapshotTasks_1294_ = lean_ctor_get(v___x_1284_, 9);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1296_ = v___x_1284_;
v_isShared_1297_ = v_isSharedCheck_1324_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_snapshotTasks_1294_);
lean_inc(v_infoState_1293_);
lean_inc(v_messages_1292_);
lean_inc(v_recordedDeps_1291_);
lean_inc(v_cache_1290_);
lean_inc(v_traceState_1285_);
lean_inc(v_auxDeclNGen_1289_);
lean_inc(v_ngen_1288_);
lean_inc(v_nextMacroScope_1287_);
lean_inc(v_env_1286_);
lean_dec(v___x_1284_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1324_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
uint64_t v_tid_1298_; lean_object* v_traces_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1323_; 
v_tid_1298_ = lean_ctor_get_uint64(v_traceState_1285_, sizeof(void*)*1);
v_traces_1299_ = lean_ctor_get(v_traceState_1285_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_traceState_1285_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1301_ = v_traceState_1285_;
v_isShared_1302_ = v_isSharedCheck_1323_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_traces_1299_);
lean_dec(v_traceState_1285_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1323_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; double v___x_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0);
v___x_1306_ = 0;
v___x_1307_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1));
v___x_1308_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1308_, 0, v_cls_1273_);
lean_ctor_set(v___x_1308_, 1, v___x_1304_);
lean_ctor_set(v___x_1308_, 2, v___x_1307_);
lean_ctor_set_float(v___x_1308_, sizeof(void*)*3, v___x_1305_);
lean_ctor_set_float(v___x_1308_, sizeof(void*)*3 + 8, v___x_1305_);
lean_ctor_set_uint8(v___x_1308_, sizeof(void*)*3 + 16, v___x_1306_);
v___x_1309_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__2));
v___x_1310_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set(v___x_1310_, 1, v_a_1280_);
lean_ctor_set(v___x_1310_, 2, v___x_1309_);
lean_inc(v_ref_1278_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v_ref_1278_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = l_Lean_PersistentArray_push___redArg(v_traces_1299_, v___x_1311_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1312_);
v___x_1314_ = v___x_1301_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1312_);
lean_ctor_set_uint64(v_reuseFailAlloc_1322_, sizeof(void*)*1, v_tid_1298_);
v___x_1314_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 4, v___x_1314_);
v___x_1316_ = v___x_1296_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_env_1286_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_nextMacroScope_1287_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_ngen_1288_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_auxDeclNGen_1289_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v_cache_1290_);
lean_ctor_set(v_reuseFailAlloc_1321_, 6, v_recordedDeps_1291_);
lean_ctor_set(v_reuseFailAlloc_1321_, 7, v_messages_1292_);
lean_ctor_set(v_reuseFailAlloc_1321_, 8, v_infoState_1293_);
lean_ctor_set(v_reuseFailAlloc_1321_, 9, v_snapshotTasks_1294_);
v___x_1316_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = lean_st_ref_put(v___y_1276_, v___x_1316_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1303_);
v___x_1319_ = v___x_1282_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1303_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___boxed(lean_object* v_cls_1326_, lean_object* v_msg_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(v_cls_1326_, v_msg_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4(lean_object* v_as_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
if (lean_obj_tag(v_as_1335_) == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
return v___x_1340_;
}
else
{
lean_object* v_toCold_1341_; lean_object* v_options_1342_; uint8_t v_hasTrace_1343_; 
v_toCold_1341_ = lean_ctor_get(v___y_1336_, 0);
v_options_1342_ = lean_ctor_get(v_toCold_1341_, 2);
v_hasTrace_1343_ = lean_ctor_get_uint8(v_options_1342_, sizeof(void*)*1);
if (v_hasTrace_1343_ == 0)
{
lean_object* v_tail_1344_; 
v_tail_1344_ = lean_ctor_get(v_as_1335_, 1);
lean_inc(v_tail_1344_);
lean_dec_ref_known(v_as_1335_, 2);
v_as_1335_ = v_tail_1344_;
goto _start;
}
else
{
lean_object* v_head_1346_; lean_object* v_tail_1347_; lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v_inheritedTraceOptions_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_head_1346_ = lean_ctor_get(v_as_1335_, 0);
lean_inc(v_head_1346_);
v_tail_1347_ = lean_ctor_get(v_as_1335_, 1);
lean_inc(v_tail_1347_);
lean_dec_ref_known(v_as_1335_, 2);
v_fst_1348_ = lean_ctor_get(v_head_1346_, 0);
lean_inc_n(v_fst_1348_, 2);
v_snd_1349_ = lean_ctor_get(v_head_1346_, 1);
lean_inc(v_snd_1349_);
lean_dec(v_head_1346_);
v_inheritedTraceOptions_1350_ = lean_ctor_get(v_toCold_1341_, 11);
v___x_1351_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__1));
v___x_1352_ = l_Lean_Name_append(v___x_1351_, v_fst_1348_);
v___x_1353_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1350_, v_options_1342_, v___x_1352_);
lean_dec(v___x_1352_);
if (v___x_1353_ == 0)
{
lean_dec(v_snd_1349_);
lean_dec(v_fst_1348_);
v_as_1335_ = v_tail_1347_;
goto _start;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_snd_1349_);
v___x_1356_ = l_Lean_MessageData_ofFormat(v___x_1355_);
v___x_1357_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(v_fst_1348_, v___x_1356_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_dec_ref_known(v___x_1357_, 1);
v_as_1335_ = v_tail_1347_;
goto _start;
}
else
{
lean_dec(v_tail_1347_);
return v___x_1357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___boxed(lean_object* v_as_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4(v_as_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(lean_object* v_keys_1364_, lean_object* v_i_1365_, lean_object* v_k_1366_){
_start:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_array_get_size(v_keys_1364_);
v___x_1368_ = lean_nat_dec_lt(v_i_1365_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec(v_i_1365_);
return v___x_1368_;
}
else
{
lean_object* v_k_x27_1369_; uint8_t v___x_1370_; 
v_k_x27_1369_ = lean_array_fget_borrowed(v_keys_1364_, v_i_1365_);
v___x_1370_ = l_Lean_instBEqExtraModUse_beq(v_k_1366_, v_k_x27_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_add(v_i_1365_, v___x_1371_);
lean_dec(v_i_1365_);
v_i_1365_ = v___x_1372_;
goto _start;
}
else
{
lean_dec(v_i_1365_);
return v___x_1368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg___boxed(lean_object* v_keys_1374_, lean_object* v_i_1375_, lean_object* v_k_1376_){
_start:
{
uint8_t v_res_1377_; lean_object* v_r_1378_; 
v_res_1377_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(v_keys_1374_, v_i_1375_, v_k_1376_);
lean_dec_ref(v_k_1376_);
lean_dec_ref(v_keys_1374_);
v_r_1378_ = lean_box(v_res_1377_);
return v_r_1378_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1379_, size_t v_x_1380_, lean_object* v_x_1381_){
_start:
{
if (lean_obj_tag(v_x_1379_) == 0)
{
lean_object* v_es_1382_; lean_object* v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; lean_object* v_j_1386_; lean_object* v___x_1387_; 
v_es_1382_ = lean_ctor_get(v_x_1379_, 0);
v___x_1383_ = lean_box(2);
v___x_1384_ = ((size_t)31ULL);
v___x_1385_ = lean_usize_land(v_x_1380_, v___x_1384_);
v_j_1386_ = lean_usize_to_nat(v___x_1385_);
v___x_1387_ = lean_array_get_borrowed(v___x_1383_, v_es_1382_, v_j_1386_);
lean_dec(v_j_1386_);
switch(lean_obj_tag(v___x_1387_))
{
case 0:
{
lean_object* v_key_1388_; uint8_t v___x_1389_; 
v_key_1388_ = lean_ctor_get(v___x_1387_, 0);
v___x_1389_ = l_Lean_instBEqExtraModUse_beq(v_x_1381_, v_key_1388_);
return v___x_1389_;
}
case 1:
{
lean_object* v_node_1390_; size_t v___x_1391_; size_t v___x_1392_; 
v_node_1390_ = lean_ctor_get(v___x_1387_, 0);
v___x_1391_ = ((size_t)5ULL);
v___x_1392_ = lean_usize_shift_right(v_x_1380_, v___x_1391_);
v_x_1379_ = v_node_1390_;
v_x_1380_ = v___x_1392_;
goto _start;
}
default: 
{
uint8_t v___x_1394_; 
v___x_1394_ = 0;
return v___x_1394_;
}
}
}
else
{
lean_object* v_ks_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_ks_1395_ = lean_ctor_get(v_x_1379_, 0);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(v_ks_1395_, v___x_1396_, v_x_1381_);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
size_t v_x_10417__boxed_1401_; uint8_t v_res_1402_; lean_object* v_r_1403_; 
v_x_10417__boxed_1401_ = lean_unbox_usize(v_x_1399_);
lean_dec(v_x_1399_);
v_res_1402_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(v_x_1398_, v_x_10417__boxed_1401_, v_x_1400_);
lean_dec_ref(v_x_1400_);
lean_dec_ref(v_x_1398_);
v_r_1403_ = lean_box(v_res_1402_);
return v_r_1403_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(lean_object* v_x_1404_, lean_object* v_x_1405_){
_start:
{
uint64_t v___x_1406_; size_t v___x_1407_; uint8_t v___x_1408_; 
v___x_1406_ = l_Lean_instHashableExtraModUse_hash(v_x_1405_);
v___x_1407_ = lean_uint64_to_usize(v___x_1406_);
v___x_1408_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(v_x_1404_, v___x_1407_, v_x_1405_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
uint8_t v_res_1411_; lean_object* v_r_1412_; 
v_res_1411_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(v_x_1409_, v_x_1410_);
lean_dec_ref(v_x_1410_);
lean_dec_ref(v_x_1409_);
v_r_1412_ = lean_box(v_res_1411_);
return v_r_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___lam__0(lean_object* v___x_1413_, lean_object* v_entry_1414_, lean_object* v_s_1415_){
_start:
{
lean_object* v_addEntryFn_1416_; lean_object* v_importedEntries_1417_; lean_object* v_state_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1426_; 
v_addEntryFn_1416_ = lean_ctor_get(v___x_1413_, 3);
lean_inc(v_addEntryFn_1416_);
lean_dec_ref(v___x_1413_);
v_importedEntries_1417_ = lean_ctor_get(v_s_1415_, 0);
v_state_1418_ = lean_ctor_get(v_s_1415_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_s_1415_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1420_ = v_s_1415_;
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_state_1418_);
lean_inc(v_importedEntries_1417_);
lean_dec(v_s_1415_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v_state_1422_; lean_object* v___x_1424_; 
v_state_1422_ = lean_apply_2(v_addEntryFn_1416_, v_state_1418_, v_entry_1414_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v_state_1422_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_importedEntries_1417_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_state_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
return v___x_1430_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1431_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__5));
v___x_1437_ = l_Lean_stringToMessageData(v___x_1436_);
return v___x_1437_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__7));
v___x_1440_ = l_Lean_stringToMessageData(v___x_1439_);
return v___x_1440_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1));
v___x_1442_ = l_Lean_stringToMessageData(v___x_1441_);
return v___x_1442_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_cls_1443_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__4));
v___x_1444_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__1));
v___x_1445_ = l_Lean_Name_append(v___x_1444_, v_cls_1443_);
return v___x_1445_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__11));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__13));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(lean_object* v_mod_1456_, uint8_t v_isMeta_1457_, lean_object* v_hint_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_env_1480_; uint8_t v_isExporting_1481_; lean_object* v_entry_1482_; lean_object* v___x_1483_; lean_object* v_env_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1478_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2);
v___x_1479_ = lean_st_ref_get(v___y_1460_);
v_env_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc_ref(v_env_1480_);
lean_dec(v___x_1479_);
v_isExporting_1481_ = lean_ctor_get_uint8(v_env_1480_, sizeof(void*)*13);
lean_dec_ref(v_env_1480_);
lean_inc(v_mod_1456_);
v_entry_1482_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1482_, 0, v_mod_1456_);
lean_ctor_set_uint8(v_entry_1482_, sizeof(void*)*1, v_isExporting_1481_);
lean_ctor_set_uint8(v_entry_1482_, sizeof(void*)*1 + 1, v_isMeta_1457_);
v___x_1483_ = lean_st_ref_get(v___y_1460_);
v_env_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc_ref(v_env_1484_);
lean_dec(v___x_1483_);
v___x_1485_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1486_ = lean_box(1);
v___x_1487_ = lean_box(0);
v___x_1488_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1478_, v___x_1485_, v_env_1484_, v___x_1486_, v___x_1487_);
v___x_1489_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(v___x_1488_, v_entry_1482_);
lean_dec(v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v_toCold_1490_; lean_object* v_options_1491_; lean_object* v_inheritedTraceOptions_1492_; uint8_t v_hasTrace_1493_; lean_object* v___f_1494_; uint8_t v___x_1495_; lean_object* v___y_1497_; 
v_toCold_1490_ = lean_ctor_get(v___y_1459_, 0);
v_options_1491_ = lean_ctor_get(v_toCold_1490_, 2);
v_inheritedTraceOptions_1492_ = lean_ctor_get(v_toCold_1490_, 11);
v_hasTrace_1493_ = lean_ctor_get_uint8(v_options_1491_, sizeof(void*)*1);
v___f_1494_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_1494_, 0, v___x_1485_);
lean_closure_set(v___f_1494_, 1, v_entry_1482_);
v___x_1495_ = 1;
if (v_hasTrace_1493_ == 0)
{
lean_dec(v_hint_1458_);
lean_dec(v_mod_1456_);
v___y_1497_ = v___y_1460_;
goto v___jp_1496_;
}
else
{
lean_object* v_cls_1515_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_cls_1515_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__4));
v___x_1535_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10);
v___x_1536_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1492_, v_options_1491_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_dec(v_hint_1458_);
lean_dec(v_mod_1456_);
v___y_1497_ = v___y_1460_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1537_; lean_object* v___y_1539_; 
v___x_1537_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12);
if (v_isExporting_1481_ == 0)
{
lean_object* v___x_1546_; 
v___x_1546_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__17));
v___y_1539_ = v___x_1546_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1547_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__18));
v___y_1539_ = v___x_1547_;
goto v___jp_1538_;
}
v___jp_1538_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_inc_ref(v___y_1539_);
v___x_1540_ = l_Lean_stringToMessageData(v___y_1539_);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1537_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
if (v_isMeta_1457_ == 0)
{
lean_object* v___x_1544_; 
v___x_1544_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__15));
v___y_1522_ = v___x_1543_;
v___y_1523_ = v___x_1544_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1545_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__16));
v___y_1522_ = v___x_1543_;
v___y_1523_ = v___x_1545_;
goto v___jp_1521_;
}
}
}
v___jp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___y_1517_);
lean_ctor_set(v___x_1519_, 1, v___y_1518_);
v___x_1520_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(v_cls_1515_, v___x_1519_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_dec_ref_known(v___x_1520_, 1);
v___y_1497_ = v___y_1460_;
goto v___jp_1496_;
}
else
{
lean_dec_ref(v___f_1494_);
return v___x_1520_;
}
}
v___jp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
lean_inc_ref(v___y_1523_);
v___x_1524_ = l_Lean_stringToMessageData(v___y_1523_);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___y_1522_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = l_Lean_MessageData_ofName(v_mod_1456_);
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = l_Lean_Name_isAnonymous(v_hint_1458_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8);
v___x_1532_ = l_Lean_MessageData_ofName(v_hint_1458_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___y_1517_ = v___x_1529_;
v___y_1518_ = v___x_1533_;
goto v___jp_1516_;
}
else
{
lean_object* v___x_1534_; 
lean_dec(v_hint_1458_);
v___x_1534_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9);
v___y_1517_ = v___x_1529_;
v___y_1518_ = v___x_1534_;
goto v___jp_1516_;
}
}
}
v___jp_1496_:
{
lean_object* v___x_1498_; lean_object* v_toEnvExtension_1499_; lean_object* v_env_1500_; lean_object* v_nextMacroScope_1501_; lean_object* v_ngen_1502_; lean_object* v_auxDeclNGen_1503_; lean_object* v_traceState_1504_; lean_object* v_recordedDeps_1505_; lean_object* v_messages_1506_; lean_object* v_infoState_1507_; lean_object* v_snapshotTasks_1508_; lean_object* v_asyncMode_1509_; uint8_t v_logWrites_1510_; lean_object* v___x_1511_; 
v___x_1498_ = lean_st_ref_take(v___y_1497_);
v_toEnvExtension_1499_ = lean_ctor_get(v___x_1485_, 0);
v_env_1500_ = lean_ctor_get(v___x_1498_, 0);
lean_inc_ref(v_env_1500_);
v_nextMacroScope_1501_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_nextMacroScope_1501_);
v_ngen_1502_ = lean_ctor_get(v___x_1498_, 2);
lean_inc_ref(v_ngen_1502_);
v_auxDeclNGen_1503_ = lean_ctor_get(v___x_1498_, 3);
lean_inc_ref(v_auxDeclNGen_1503_);
v_traceState_1504_ = lean_ctor_get(v___x_1498_, 4);
lean_inc_ref(v_traceState_1504_);
v_recordedDeps_1505_ = lean_ctor_get(v___x_1498_, 6);
lean_inc_ref(v_recordedDeps_1505_);
v_messages_1506_ = lean_ctor_get(v___x_1498_, 7);
lean_inc_ref(v_messages_1506_);
v_infoState_1507_ = lean_ctor_get(v___x_1498_, 8);
lean_inc_ref(v_infoState_1507_);
v_snapshotTasks_1508_ = lean_ctor_get(v___x_1498_, 9);
lean_inc_ref(v_snapshotTasks_1508_);
lean_dec(v___x_1498_);
v_asyncMode_1509_ = lean_ctor_get(v_toEnvExtension_1499_, 2);
v_logWrites_1510_ = lean_ctor_get_uint8(v_toEnvExtension_1499_, sizeof(void*)*6);
v___x_1511_ = lean_box(0);
if (v_logWrites_1510_ == 0)
{
lean_object* v___x_1512_; 
lean_inc_ref(v_toEnvExtension_1499_);
v___x_1512_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1499_, v_env_1500_, v___f_1494_, v_asyncMode_1509_, v___x_1487_, v___x_1495_);
v___y_1463_ = v_snapshotTasks_1508_;
v___y_1464_ = v_auxDeclNGen_1503_;
v___y_1465_ = v_nextMacroScope_1501_;
v___y_1466_ = v___x_1511_;
v___y_1467_ = v_recordedDeps_1505_;
v___y_1468_ = v_ngen_1502_;
v___y_1469_ = v_infoState_1507_;
v___y_1470_ = v_traceState_1504_;
v___y_1471_ = v___y_1497_;
v___y_1472_ = v_messages_1506_;
v___y_1473_ = v___x_1512_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_inc_ref_n(v_toEnvExtension_1499_, 2);
v___x_1513_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1499_, v_env_1500_);
lean_dec_ref(v_env_1500_);
v___x_1514_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1499_, v___x_1513_, v___f_1494_, v_asyncMode_1509_, v___x_1487_, v___x_1495_);
v___y_1463_ = v_snapshotTasks_1508_;
v___y_1464_ = v_auxDeclNGen_1503_;
v___y_1465_ = v_nextMacroScope_1501_;
v___y_1466_ = v___x_1511_;
v___y_1467_ = v_recordedDeps_1505_;
v___y_1468_ = v_ngen_1502_;
v___y_1469_ = v_infoState_1507_;
v___y_1470_ = v_traceState_1504_;
v___y_1471_ = v___y_1497_;
v___y_1472_ = v_messages_1506_;
v___y_1473_ = v___x_1514_;
goto v___jp_1462_;
}
}
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec_ref_known(v_entry_1482_, 1);
lean_dec(v_hint_1458_);
lean_dec(v_mod_1456_);
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
v___jp_1462_:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1474_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1);
v___x_1475_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1475_, 0, v___y_1473_);
lean_ctor_set(v___x_1475_, 1, v___y_1465_);
lean_ctor_set(v___x_1475_, 2, v___y_1468_);
lean_ctor_set(v___x_1475_, 3, v___y_1464_);
lean_ctor_set(v___x_1475_, 4, v___y_1470_);
lean_ctor_set(v___x_1475_, 5, v___x_1474_);
lean_ctor_set(v___x_1475_, 6, v___y_1467_);
lean_ctor_set(v___x_1475_, 7, v___y_1472_);
lean_ctor_set(v___x_1475_, 8, v___y_1469_);
lean_ctor_set(v___x_1475_, 9, v___y_1463_);
v___x_1476_ = lean_st_ref_put(v___y_1471_, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___y_1466_);
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_1550_, lean_object* v_isMeta_1551_, lean_object* v_hint_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v_isMeta_boxed_1556_; lean_object* v_res_1557_; 
v_isMeta_boxed_1556_ = lean_unbox(v_isMeta_1551_);
v_res_1557_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(v_mod_1550_, v_isMeta_boxed_1556_, v_hint_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(lean_object* v_a_1558_, lean_object* v_x_1559_){
_start:
{
if (lean_obj_tag(v_x_1559_) == 0)
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_box(0);
return v___x_1560_;
}
else
{
lean_object* v_key_1561_; lean_object* v_value_1562_; lean_object* v_tail_1563_; uint8_t v___x_1564_; 
v_key_1561_ = lean_ctor_get(v_x_1559_, 0);
v_value_1562_ = lean_ctor_get(v_x_1559_, 1);
v_tail_1563_ = lean_ctor_get(v_x_1559_, 2);
v___x_1564_ = lean_name_eq(v_key_1561_, v_a_1558_);
if (v___x_1564_ == 0)
{
v_x_1559_ = v_tail_1563_;
goto _start;
}
else
{
lean_object* v___x_1566_; 
lean_inc(v_value_1562_);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_value_1562_);
return v___x_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_a_1567_, lean_object* v_x_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(v_a_1567_, v_x_1568_);
lean_dec(v_x_1568_);
lean_dec(v_a_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(lean_object* v_m_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_buckets_1572_; lean_object* v___x_1573_; uint64_t v___y_1575_; 
v_buckets_1572_ = lean_ctor_get(v_m_1570_, 1);
v___x_1573_ = lean_array_get_size(v_buckets_1572_);
if (lean_obj_tag(v_a_1571_) == 0)
{
uint64_t v___x_1589_; 
v___x_1589_ = 1723ULL;
v___y_1575_ = v___x_1589_;
goto v___jp_1574_;
}
else
{
uint64_t v_hash_1590_; 
v_hash_1590_ = lean_ctor_get_uint64(v_a_1571_, sizeof(void*)*2);
v___y_1575_ = v_hash_1590_;
goto v___jp_1574_;
}
v___jp_1574_:
{
uint64_t v___x_1576_; uint64_t v___x_1577_; uint64_t v_fold_1578_; uint64_t v___x_1579_; uint64_t v___x_1580_; uint64_t v___x_1581_; size_t v___x_1582_; size_t v___x_1583_; size_t v___x_1584_; size_t v___x_1585_; size_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1576_ = 32ULL;
v___x_1577_ = lean_uint64_shift_right(v___y_1575_, v___x_1576_);
v_fold_1578_ = lean_uint64_xor(v___y_1575_, v___x_1577_);
v___x_1579_ = 16ULL;
v___x_1580_ = lean_uint64_shift_right(v_fold_1578_, v___x_1579_);
v___x_1581_ = lean_uint64_xor(v_fold_1578_, v___x_1580_);
v___x_1582_ = lean_uint64_to_usize(v___x_1581_);
v___x_1583_ = lean_usize_of_nat(v___x_1573_);
v___x_1584_ = ((size_t)1ULL);
v___x_1585_ = lean_usize_sub(v___x_1583_, v___x_1584_);
v___x_1586_ = lean_usize_land(v___x_1582_, v___x_1585_);
v___x_1587_ = lean_array_uget_borrowed(v_buckets_1572_, v___x_1586_);
v___x_1588_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(v_a_1571_, v___x_1587_);
return v___x_1588_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(v_m_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_m_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4(lean_object* v___x_1594_, lean_object* v_declName_1595_, lean_object* v_as_1596_, size_t v_sz_1597_, size_t v_i_1598_, lean_object* v_b_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_usize_dec_lt(v_i_1598_, v_sz_1597_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_dec(v_declName_1595_);
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_b_1599_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v_modules_1606_; lean_object* v___x_1607_; lean_object* v_a_1608_; lean_object* v___x_1609_; lean_object* v_toImport_1610_; lean_object* v_module_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1605_ = l_Lean_Environment_header(v___x_1594_);
v_modules_1606_ = lean_ctor_get(v___x_1605_, 3);
lean_inc_ref(v_modules_1606_);
lean_dec_ref(v___x_1605_);
v___x_1607_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1608_ = lean_array_uget_borrowed(v_as_1596_, v_i_1598_);
v___x_1609_ = lean_array_get(v___x_1607_, v_modules_1606_, v_a_1608_);
lean_dec_ref(v_modules_1606_);
v_toImport_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_toImport_1610_);
lean_dec(v___x_1609_);
v_module_1611_ = lean_ctor_get(v_toImport_1610_, 0);
lean_inc(v_module_1611_);
lean_dec_ref(v_toImport_1610_);
v___x_1612_ = lean_box(0);
v___x_1613_ = 0;
lean_inc(v_declName_1595_);
v___x_1614_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(v_module_1611_, v___x_1613_, v_declName_1595_, v___y_1600_, v___y_1601_);
if (lean_obj_tag(v___x_1614_) == 0)
{
size_t v___x_1615_; size_t v___x_1616_; 
lean_dec_ref_known(v___x_1614_, 1);
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1598_, v___x_1615_);
v_i_1598_ = v___x_1616_;
v_b_1599_ = v___x_1612_;
goto _start;
}
else
{
lean_dec(v_declName_1595_);
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4___boxed(lean_object* v___x_1618_, lean_object* v_declName_1619_, lean_object* v_as_1620_, lean_object* v_sz_1621_, lean_object* v_i_1622_, lean_object* v_b_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
size_t v_sz_boxed_1627_; size_t v_i_boxed_1628_; lean_object* v_res_1629_; 
v_sz_boxed_1627_ = lean_unbox_usize(v_sz_1621_);
lean_dec(v_sz_1621_);
v_i_boxed_1628_ = lean_unbox_usize(v_i_1622_);
lean_dec(v_i_1622_);
v_res_1629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4(v___x_1618_, v_declName_1619_, v_as_1620_, v_sz_boxed_1627_, v_i_boxed_1628_, v_b_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v_as_1620_);
lean_dec_ref(v___x_1618_);
return v_res_1629_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2(lean_object* v_declName_1633_, uint8_t v_isMeta_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_env_1643_; lean_object* v___y_1645_; lean_object* v___x_1658_; 
v___x_1638_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0);
v___x_1639_ = lean_st_ref_get(v___y_1636_);
v_env_1643_ = lean_ctor_get(v___x_1639_, 0);
lean_inc_ref(v_env_1643_);
lean_dec(v___x_1639_);
v___x_1658_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1643_, v_declName_1633_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_dec_ref(v_env_1643_);
lean_dec(v_declName_1633_);
goto v___jp_1640_;
}
else
{
lean_object* v_val_1659_; lean_object* v___x_1660_; lean_object* v_modules_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_val_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_val_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v___x_1660_ = l_Lean_Environment_header(v_env_1643_);
v_modules_1661_ = lean_ctor_get(v___x_1660_, 3);
lean_inc_ref(v_modules_1661_);
lean_dec_ref(v___x_1660_);
v___x_1662_ = lean_array_get_size(v_modules_1661_);
v___x_1663_ = lean_nat_dec_lt(v_val_1659_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_dec_ref(v_modules_1661_);
lean_dec(v_val_1659_);
lean_dec_ref(v_env_1643_);
lean_dec(v_declName_1633_);
goto v___jp_1640_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___y_1667_; 
v___x_1664_ = lean_array_fget(v_modules_1661_, v_val_1659_);
lean_dec(v_val_1659_);
lean_dec_ref(v_modules_1661_);
v___x_1665_ = lean_st_ref_get(v___y_1636_);
if (v_isMeta_1634_ == 0)
{
lean_dec(v___x_1665_);
v___y_1667_ = v_isMeta_1634_;
goto v___jp_1666_;
}
else
{
lean_object* v_env_1678_; uint8_t v___x_1679_; 
v_env_1678_ = lean_ctor_get(v___x_1665_, 0);
lean_inc_ref(v_env_1678_);
lean_dec(v___x_1665_);
lean_inc(v_declName_1633_);
v___x_1679_ = l_Lean_isMarkedMeta(v_env_1678_, v_declName_1633_);
if (v___x_1679_ == 0)
{
v___y_1667_ = v_isMeta_1634_;
goto v___jp_1666_;
}
else
{
uint8_t v___x_1680_; 
v___x_1680_ = 0;
v___y_1667_ = v___x_1680_;
goto v___jp_1666_;
}
}
v___jp_1666_:
{
lean_object* v_toImport_1668_; lean_object* v_module_1669_; lean_object* v___x_1670_; 
v_toImport_1668_ = lean_ctor_get(v___x_1664_, 0);
lean_inc_ref(v_toImport_1668_);
lean_dec(v___x_1664_);
v_module_1669_ = lean_ctor_get(v_toImport_1668_, 0);
lean_inc(v_module_1669_);
lean_dec_ref(v_toImport_1668_);
lean_inc(v_declName_1633_);
v___x_1670_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(v_module_1669_, v___y_1667_, v_declName_1633_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec_ref_known(v___x_1670_, 1);
v___x_1671_ = l_Lean_indirectModUseExt;
v___x_1672_ = lean_box(1);
v___x_1673_ = lean_box(0);
lean_inc_ref(v_env_1643_);
v___x_1674_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1638_, v___x_1671_, v_env_1643_, v___x_1672_, v___x_1673_);
v___x_1675_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(v___x_1674_, v_declName_1633_);
lean_dec(v___x_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__1));
v___y_1645_ = v___x_1676_;
goto v___jp_1644_;
}
else
{
lean_object* v_val_1677_; 
v_val_1677_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_val_1677_);
lean_dec_ref_known(v___x_1675_, 1);
v___y_1645_ = v_val_1677_;
goto v___jp_1644_;
}
}
else
{
lean_dec_ref(v_env_1643_);
lean_dec(v_declName_1633_);
return v___x_1670_;
}
}
}
}
v___jp_1640_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_box(0);
v___x_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
v___jp_1644_:
{
lean_object* v___x_1646_; size_t v_sz_1647_; size_t v___x_1648_; lean_object* v___x_1649_; 
v___x_1646_ = lean_box(0);
v_sz_1647_ = lean_array_size(v___y_1645_);
v___x_1648_ = ((size_t)0ULL);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4(v_env_1643_, v_declName_1633_, v___y_1645_, v_sz_1647_, v___x_1648_, v___x_1646_, v___y_1635_, v___y_1636_);
lean_dec_ref(v___y_1645_);
lean_dec_ref(v_env_1643_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; 
v_unused_1657_ = lean_ctor_get(v___x_1649_, 0);
lean_dec(v_unused_1657_);
v___x_1651_ = v___x_1649_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_dec(v___x_1649_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1646_);
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1646_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
else
{
return v___x_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___boxed(lean_object* v_declName_1681_, lean_object* v_isMeta_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
uint8_t v_isMeta_boxed_1686_; lean_object* v_res_1687_; 
v_isMeta_boxed_1686_ = lean_unbox(v_isMeta_1682_);
v_res_1687_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2(v_declName_1681_, v_isMeta_boxed_1686_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(lean_object* v_as_x27_1688_, lean_object* v_b_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
if (lean_obj_tag(v_as_x27_1688_) == 0)
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_b_1689_);
return v___x_1693_;
}
else
{
lean_object* v_head_1694_; lean_object* v_tail_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; 
v_head_1694_ = lean_ctor_get(v_as_x27_1688_, 0);
v_tail_1695_ = lean_ctor_get(v_as_x27_1688_, 1);
v___x_1696_ = lean_box(0);
v___x_1697_ = 1;
lean_inc(v_head_1694_);
v___x_1698_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2(v_head_1694_, v___x_1697_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_dec_ref_known(v___x_1698_, 1);
v_as_x27_1688_ = v_tail_1695_;
v_b_1689_ = v___x_1696_;
goto _start;
}
else
{
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1700_, lean_object* v_b_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(v_as_x27_1700_, v_b_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v_as_x27_1700_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(lean_object* v_env_1706_, lean_object* v_declName_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
uint8_t v___x_1710_; lean_object* v_env_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; uint8_t v___x_1714_; 
v___x_1710_ = 0;
v_env_1711_ = l_Lean_Environment_setExporting(v_env_1706_, v___x_1710_);
lean_inc(v_declName_1707_);
v___x_1712_ = l_Lean_mkPrivateName(v_env_1711_, v_declName_1707_);
v___x_1713_ = 1;
lean_inc_ref(v_env_1711_);
v___x_1714_ = l_Lean_Environment_contains(v_env_1711_, v___x_1712_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1715_ = l_Lean_privateToUserName(v_declName_1707_);
v___x_1716_ = l_Lean_Environment_contains(v_env_1711_, v___x_1715_, v___x_1713_);
v___x_1717_ = lean_box(v___x_1716_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v___y_1709_);
return v___x_1718_;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
lean_dec_ref(v_env_1711_);
lean_dec(v_declName_1707_);
v___x_1719_ = lean_box(v___x_1714_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set(v___x_1720_, 1, v___y_1709_);
return v___x_1720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0___boxed(lean_object* v_env_1721_, lean_object* v_declName_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(v_env_1721_, v_declName_1722_, v___y_1723_, v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(lean_object* v_x_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; lean_object* v_toCold_1732_; lean_object* v_env_1733_; lean_object* v_currRecDepth_1734_; lean_object* v_ref_1735_; lean_object* v_maxRecDepth_1736_; lean_object* v_currNamespace_1737_; lean_object* v_openDecls_1738_; lean_object* v_quotContext_1739_; lean_object* v_currMacroScope_1740_; lean_object* v___f_1741_; lean_object* v___f_1742_; lean_object* v___x_1743_; lean_object* v___f_1744_; lean_object* v___f_1745_; lean_object* v___f_1746_; lean_object* v_methods_1747_; lean_object* v___x_1748_; lean_object* v_nextMacroScope_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1731_ = lean_st_ref_get(v___y_1729_);
v_toCold_1732_ = lean_ctor_get(v___y_1728_, 0);
v_env_1733_ = lean_ctor_get(v___x_1731_, 0);
lean_inc_ref_n(v_env_1733_, 4);
lean_dec(v___x_1731_);
v_currRecDepth_1734_ = lean_ctor_get(v___y_1728_, 1);
v_ref_1735_ = lean_ctor_get(v___y_1728_, 2);
v_maxRecDepth_1736_ = lean_ctor_get(v_toCold_1732_, 3);
v_currNamespace_1737_ = lean_ctor_get(v_toCold_1732_, 4);
v_openDecls_1738_ = lean_ctor_get(v_toCold_1732_, 5);
v_quotContext_1739_ = lean_ctor_get(v_toCold_1732_, 8);
v_currMacroScope_1740_ = lean_ctor_get(v_toCold_1732_, 9);
v___f_1741_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1741_, 0, v_env_1733_);
v___f_1742_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1742_, 0, v_env_1733_);
v___x_1743_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1728_);
lean_inc_n(v_currNamespace_1737_, 3);
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1744_, 0, v_currNamespace_1737_);
lean_inc_n(v_openDecls_1738_, 2);
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1745_, 0, v_env_1733_);
lean_closure_set(v___f_1745_, 1, v___x_1743_);
lean_closure_set(v___f_1745_, 2, v_currNamespace_1737_);
lean_closure_set(v___f_1745_, 3, v_openDecls_1738_);
v___f_1746_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1746_, 0, v_env_1733_);
lean_closure_set(v___f_1746_, 1, v_currNamespace_1737_);
lean_closure_set(v___f_1746_, 2, v_openDecls_1738_);
v_methods_1747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1747_, 0, v___f_1742_);
lean_ctor_set(v_methods_1747_, 1, v___f_1744_);
lean_ctor_set(v_methods_1747_, 2, v___f_1741_);
lean_ctor_set(v_methods_1747_, 3, v___f_1746_);
lean_ctor_set(v_methods_1747_, 4, v___f_1745_);
v___x_1748_ = lean_st_ref_get(v___y_1729_);
v_nextMacroScope_1749_ = lean_ctor_get(v___x_1748_, 1);
lean_inc(v_nextMacroScope_1749_);
lean_dec(v___x_1748_);
lean_inc(v_ref_1735_);
lean_inc(v_maxRecDepth_1736_);
lean_inc(v_currRecDepth_1734_);
lean_inc(v_currMacroScope_1740_);
lean_inc(v_quotContext_1739_);
v___x_1750_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1750_, 0, v_methods_1747_);
lean_ctor_set(v___x_1750_, 1, v_quotContext_1739_);
lean_ctor_set(v___x_1750_, 2, v_currMacroScope_1740_);
lean_ctor_set(v___x_1750_, 3, v_currRecDepth_1734_);
lean_ctor_set(v___x_1750_, 4, v_maxRecDepth_1736_);
lean_ctor_set(v___x_1750_, 5, v_ref_1735_);
v___x_1751_ = lean_box(0);
v___x_1752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1752_, 0, v_nextMacroScope_1749_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
lean_ctor_set(v___x_1752_, 2, v___x_1751_);
v___x_1753_ = lean_apply_2(v_x_1727_, v___x_1750_, v___x_1752_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v_a_1755_; lean_object* v_macroScope_1756_; lean_object* v_traceMsgs_1757_; lean_object* v_expandedMacroDecls_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 1);
lean_inc(v_a_1754_);
v_a_1755_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1753_, 2);
v_macroScope_1756_ = lean_ctor_get(v_a_1754_, 0);
lean_inc(v_macroScope_1756_);
v_traceMsgs_1757_ = lean_ctor_get(v_a_1754_, 1);
lean_inc(v_traceMsgs_1757_);
v_expandedMacroDecls_1758_ = lean_ctor_get(v_a_1754_, 2);
lean_inc(v_expandedMacroDecls_1758_);
lean_dec(v_a_1754_);
v___x_1759_ = lean_box(0);
v___x_1760_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(v_expandedMacroDecls_1758_, v___x_1759_, v___y_1728_, v___y_1729_);
lean_dec(v_expandedMacroDecls_1758_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v___x_1761_; lean_object* v_env_1762_; lean_object* v_ngen_1763_; lean_object* v_auxDeclNGen_1764_; lean_object* v_traceState_1765_; lean_object* v_cache_1766_; lean_object* v_recordedDeps_1767_; lean_object* v_messages_1768_; lean_object* v_infoState_1769_; lean_object* v_snapshotTasks_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref_known(v___x_1760_, 1);
v___x_1761_ = lean_st_ref_take(v___y_1729_);
v_env_1762_ = lean_ctor_get(v___x_1761_, 0);
v_ngen_1763_ = lean_ctor_get(v___x_1761_, 2);
v_auxDeclNGen_1764_ = lean_ctor_get(v___x_1761_, 3);
v_traceState_1765_ = lean_ctor_get(v___x_1761_, 4);
v_cache_1766_ = lean_ctor_get(v___x_1761_, 5);
v_recordedDeps_1767_ = lean_ctor_get(v___x_1761_, 6);
v_messages_1768_ = lean_ctor_get(v___x_1761_, 7);
v_infoState_1769_ = lean_ctor_get(v___x_1761_, 8);
v_snapshotTasks_1770_ = lean_ctor_get(v___x_1761_, 9);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v___x_1761_, 1);
lean_dec(v_unused_1797_);
v___x_1772_ = v___x_1761_;
v_isShared_1773_ = v_isSharedCheck_1796_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_snapshotTasks_1770_);
lean_inc(v_infoState_1769_);
lean_inc(v_messages_1768_);
lean_inc(v_recordedDeps_1767_);
lean_inc(v_cache_1766_);
lean_inc(v_traceState_1765_);
lean_inc(v_auxDeclNGen_1764_);
lean_inc(v_ngen_1763_);
lean_inc(v_env_1762_);
lean_dec(v___x_1761_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1796_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v_macroScope_1756_);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_env_1762_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_macroScope_1756_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_ngen_1763_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v_auxDeclNGen_1764_);
lean_ctor_set(v_reuseFailAlloc_1795_, 4, v_traceState_1765_);
lean_ctor_set(v_reuseFailAlloc_1795_, 5, v_cache_1766_);
lean_ctor_set(v_reuseFailAlloc_1795_, 6, v_recordedDeps_1767_);
lean_ctor_set(v_reuseFailAlloc_1795_, 7, v_messages_1768_);
lean_ctor_set(v_reuseFailAlloc_1795_, 8, v_infoState_1769_);
lean_ctor_set(v_reuseFailAlloc_1795_, 9, v_snapshotTasks_1770_);
v___x_1775_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = lean_st_ref_put(v___y_1729_, v___x_1775_);
v___x_1777_ = l_List_reverse___redArg(v_traceMsgs_1757_);
v___x_1778_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4(v___x_1777_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v___x_1778_, 0);
lean_dec(v_unused_1786_);
v___x_1780_ = v___x_1778_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_dec(v___x_1778_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_a_1755_);
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1755_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v_a_1755_);
v_a_1787_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1778_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1778_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_traceMsgs_1757_);
lean_dec(v_macroScope_1756_);
lean_dec(v_a_1755_);
v_a_1798_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1760_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1760_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1806_; 
v_a_1806_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1753_, 2);
if (lean_obj_tag(v_a_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v_a_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v_a_1807_ = lean_ctor_get(v_a_1806_, 0);
lean_inc(v_a_1807_);
v_a_1808_ = lean_ctor_get(v_a_1806_, 1);
lean_inc_ref(v_a_1808_);
lean_dec_ref_known(v_a_1806_, 2);
v___x_1809_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___closed__0));
v___x_1810_ = lean_string_dec_eq(v_a_1808_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_a_1808_);
v___x_1812_ = l_Lean_MessageData_ofFormat(v___x_1811_);
v___x_1813_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(v_a_1807_, v___x_1812_, v___y_1728_, v___y_1729_);
lean_dec(v_a_1807_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; 
lean_dec_ref(v_a_1808_);
v___x_1814_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(v_a_1807_);
return v___x_1814_;
}
}
else
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg();
return v___x_1815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___boxed(lean_object* v_x_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(v_x_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
return v_res_1820_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__1));
v___x_1825_ = l_Lean_MessageData_ofFormat(v___x_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(lean_object* v_stx_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___y_1831_; lean_object* v_a_1832_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v_env_1841_; lean_object* v___x_1842_; lean_object* v_toEnvExtension_1843_; lean_object* v_asyncMode_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1836_ = lean_box(1);
v___x_1837_ = lean_st_ref_get(v_a_1828_);
v_env_1841_ = lean_ctor_get(v___x_1837_, 0);
lean_inc_ref_n(v_env_1841_, 2);
lean_dec(v___x_1837_);
v___x_1842_ = l_Lean_Elab_deprecatedSyntaxReplacementExt;
v_toEnvExtension_1843_ = lean_ctor_get(v___x_1842_, 0);
v_asyncMode_1844_ = lean_ctor_get(v_toEnvExtension_1843_, 2);
v___x_1845_ = lean_box(0);
v___x_1846_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1836_, v___x_1842_, v_env_1841_, v_asyncMode_1844_, v___x_1845_);
lean_inc(v_stx_1826_);
v___x_1847_ = l_Lean_Syntax_getKind(v_stx_1826_);
v___x_1848_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1846_, v___x_1847_);
lean_dec(v___x_1846_);
if (lean_obj_tag(v___x_1848_) == 1)
{
lean_object* v_val_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1953_; 
v_val_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1953_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_val_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1953_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1853_ = l_Lean_Parser_getSyntaxNodeKindCategories(v_env_1841_, v___x_1847_);
v___x_1854_ = lean_array_get_size(v___x_1853_);
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = lean_nat_dec_eq(v___x_1854_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
lean_dec_ref(v___x_1853_);
lean_dec(v_val_1849_);
lean_dec(v_stx_1826_);
v___x_1857_ = l_Lean_MessageData_nil;
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1857_);
v___x_1859_ = v___x_1851_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
else
{
lean_object* v___x_1861_; 
v___x_1861_ = l_Lean_Syntax_getRange_x3f(v_stx_1826_, v___x_1856_);
if (lean_obj_tag(v___x_1861_) == 1)
{
lean_object* v_toCold_1862_; lean_object* v_val_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1948_; 
lean_del_object(v___x_1851_);
v_toCold_1862_ = lean_ctor_get(v_a_1827_, 0);
v_val_1863_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1865_ = v___x_1861_;
v_isShared_1866_ = v_isSharedCheck_1948_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_val_1863_);
lean_dec(v___x_1861_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1948_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_currRecDepth_1867_; lean_object* v_ref_1868_; uint16_t v_optionFlags_1869_; uint8_t v_suppressElabErrors_1870_; uint8_t v_checkDeprecated_1871_; uint8_t v_isRecordingDeps_1872_; lean_object* v_fileMap_1873_; lean_object* v___x_1874_; 
v_currRecDepth_1867_ = lean_ctor_get(v_a_1827_, 1);
v_ref_1868_ = lean_ctor_get(v_a_1827_, 2);
v_optionFlags_1869_ = lean_ctor_get_uint16(v_a_1827_, sizeof(void*)*3);
v_suppressElabErrors_1870_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3 + 2);
v_checkDeprecated_1871_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1872_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3 + 4);
v_fileMap_1873_ = lean_ctor_get(v_toCold_1862_, 1);
v___x_1874_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1826_, v___x_1856_, v___x_1856_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_del_object(v___x_1865_);
lean_dec(v_val_1863_);
lean_dec_ref(v___x_1853_);
lean_dec(v_val_1849_);
lean_dec(v_stx_1826_);
goto v___jp_1838_;
}
else
{
lean_object* v_val_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1947_; 
v_val_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1947_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_val_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1947_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_str_1879_; lean_object* v_source_1880_; uint8_t v___x_1881_; 
v_str_1879_ = lean_ctor_get(v_val_1875_, 0);
lean_inc_ref(v_str_1879_);
lean_dec(v_val_1875_);
v_source_1880_ = lean_ctor_get(v_fileMap_1873_, 0);
v___x_1881_ = lean_string_dec_eq(v_str_1879_, v_source_1880_);
lean_dec_ref(v_str_1879_);
if (v___x_1881_ == 0)
{
lean_del_object(v___x_1877_);
lean_del_object(v___x_1865_);
lean_dec(v_val_1863_);
lean_dec_ref(v___x_1853_);
lean_dec(v_val_1849_);
lean_dec(v_stx_1826_);
goto v___jp_1838_;
}
else
{
lean_object* v___x_1882_; lean_object* v___f_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_box(v___x_1881_);
v___f_1883_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1883_, 0, v___x_1882_);
lean_inc(v_stx_1826_);
v___x_1884_ = l_Lean_Syntax_find_x3f(v_stx_1826_, v___f_1883_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_array_fget(v___x_1853_, v___x_1885_);
lean_dec_ref(v___x_1853_);
v___x_1887_ = 0;
v___x_1888_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe(v_val_1849_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v_ref_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
lean_inc(v_stx_1826_);
v___x_1890_ = l_Lean_Syntax_unsetTrailing(v_stx_1826_);
v___x_1891_ = lean_apply_1(v_a_1889_, v___x_1890_);
v_ref_1892_ = l_Lean_replaceRef(v_stx_1826_, v_ref_1868_);
lean_inc(v_currRecDepth_1867_);
lean_inc_ref(v_toCold_1862_);
v___x_1893_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1893_, 0, v_toCold_1862_);
lean_ctor_set(v___x_1893_, 1, v_currRecDepth_1867_);
lean_ctor_set(v___x_1893_, 2, v_ref_1892_);
lean_ctor_set_uint16(v___x_1893_, sizeof(void*)*3, v_optionFlags_1869_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 2, v_suppressElabErrors_1870_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 3, v_checkDeprecated_1871_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 4, v_isRecordingDeps_1872_);
v___x_1894_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(v___x_1891_, v___x_1893_, v_a_1828_);
lean_dec_ref_known(v___x_1893_, 3);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v___x_1894_, 1);
v___x_1896_ = l_Lean_Syntax_eraseQuoteMacroScopes(v_a_1895_);
lean_inc(v_stx_1826_);
v___x_1897_ = l_Lean_Elab_DeprecatedSyntax_formatReplacement(v___x_1886_, v_stx_1826_, v___x_1896_, v_val_1863_, v_a_1827_, v_a_1828_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2, &l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2_once, _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v_a_1898_);
v___x_1901_ = v___x_1865_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1898_);
v___x_1901_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1902_ = lean_box(0);
v___x_1903_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
lean_ctor_set(v___x_1903_, 2, v___x_1902_);
lean_ctor_set(v___x_1903_, 3, v___x_1902_);
lean_ctor_set(v___x_1903_, 4, v___x_1902_);
lean_ctor_set(v___x_1903_, 5, v___x_1902_);
v___x_1904_ = 0;
v___x_1905_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1884_);
lean_ctor_set(v___x_1905_, 2, v___x_1884_);
lean_ctor_set_uint8(v___x_1905_, sizeof(void*)*3, v___x_1904_);
v___x_1906_ = lean_mk_empty_array_with_capacity(v___x_1855_);
v___x_1907_ = lean_array_push(v___x_1906_, v___x_1905_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v_stx_1826_);
v___x_1909_ = v___x_1877_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_stx_1826_);
v___x_1909_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_MessageData_hint(v___x_1899_, v___x_1907_, v___x_1909_, v___x_1902_, v___x_1887_, v_a_1827_, v_a_1828_);
lean_dec_ref(v___x_1907_);
if (lean_obj_tag(v___x_1910_) == 0)
{
return v___x_1910_;
}
else
{
lean_object* v_a_1911_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
v___y_1831_ = v___x_1910_;
v_a_1832_ = v_a_1911_;
goto v___jp_1830_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_del_object(v___x_1877_);
lean_del_object(v___x_1865_);
lean_dec(v_stx_1826_);
v_a_1914_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1897_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1897_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
lean_inc(v_a_1914_);
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
v___y_1831_ = v___x_1919_;
v_a_1832_ = v_a_1914_;
goto v___jp_1830_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v___x_1886_);
lean_del_object(v___x_1877_);
lean_del_object(v___x_1865_);
lean_dec(v_val_1863_);
lean_dec(v_stx_1826_);
v_a_1922_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1894_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1894_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
lean_inc(v_a_1922_);
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
v___y_1831_ = v___x_1927_;
v_a_1832_ = v_a_1922_;
goto v___jp_1830_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v___x_1886_);
lean_del_object(v___x_1877_);
lean_del_object(v___x_1865_);
lean_dec(v_val_1863_);
lean_dec(v_stx_1826_);
v_a_1930_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1888_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1888_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
lean_inc(v_a_1930_);
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
v___y_1831_ = v___x_1935_;
v_a_1832_ = v_a_1930_;
goto v___jp_1830_;
}
}
}
}
else
{
lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1945_; 
lean_del_object(v___x_1877_);
lean_del_object(v___x_1865_);
lean_dec(v_val_1863_);
lean_dec_ref(v___x_1853_);
lean_dec(v_val_1849_);
lean_dec(v_stx_1826_);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1884_, 0);
lean_dec(v_unused_1946_);
v___x_1939_ = v___x_1884_;
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
else
{
lean_dec(v___x_1884_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = l_Lean_MessageData_nil;
if (v_isShared_1940_ == 0)
{
lean_ctor_set_tag(v___x_1939_, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
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
lean_object* v___x_1949_; lean_object* v___x_1951_; 
lean_dec(v___x_1861_);
lean_dec_ref(v___x_1853_);
lean_dec(v_val_1849_);
lean_dec(v_stx_1826_);
v___x_1949_ = l_Lean_MessageData_nil;
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1949_);
v___x_1951_ = v___x_1851_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v___x_1848_);
lean_dec(v___x_1847_);
lean_dec_ref(v_env_1841_);
lean_dec(v_stx_1826_);
v___x_1954_ = l_Lean_MessageData_nil;
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
v___jp_1830_:
{
uint8_t v___x_1833_; 
v___x_1833_ = l_Lean_Exception_isInterrupt(v_a_1832_);
lean_dec_ref(v_a_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec_ref(v___y_1831_);
v___x_1834_ = l_Lean_MessageData_nil;
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
else
{
return v___y_1831_;
}
}
v___jp_1838_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = l_Lean_MessageData_nil;
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___boxed(lean_object* v_stx_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(v_stx_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1(lean_object* v_00_u03b1_1961_, lean_object* v_x_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(v_x_1962_, v___y_1964_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1966_, lean_object* v_x_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1(v_00_u03b1_1966_, v_x_1967_, v___y_1968_, v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec_ref(v_x_1967_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6(lean_object* v_00_u03b1_1971_, lean_object* v_ref_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(v_ref_1972_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1977_, lean_object* v_ref_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6(v_00_u03b1_1977_, v_ref_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7(lean_object* v_00_u03b1_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg();
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___boxed(lean_object* v_00_u03b1_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7(v_00_u03b1_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0(lean_object* v_00_u03b1_1993_, lean_object* v_x_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(v_x_1994_, v___y_1995_, v___y_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___boxed(lean_object* v_00_u03b1_1999_, lean_object* v_x_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0(v_00_u03b1_1999_, v_x_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3(lean_object* v_as_2005_, lean_object* v_as_x27_2006_, lean_object* v_b_2007_, lean_object* v_a_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(v_as_x27_2006_, v_b_2007_, v___y_2009_, v___y_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___boxed(lean_object* v_as_2013_, lean_object* v_as_x27_2014_, lean_object* v_b_2015_, lean_object* v_a_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3(v_as_2013_, v_as_x27_2014_, v_b_2015_, v_a_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v_as_x27_2014_);
lean_dec(v_as_2013_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5(lean_object* v_00_u03b1_2021_, lean_object* v_ref_2022_, lean_object* v_msg_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(v_ref_2022_, v_msg_2023_, v___y_2024_, v___y_2025_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2028_, lean_object* v_ref_2029_, lean_object* v_msg_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5(v_00_u03b1_2028_, v_ref_2029_, v_msg_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v_ref_2029_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2035_, lean_object* v_m_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(v_m_2036_, v_a_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2039_, lean_object* v_m_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5(v_00_u03b2_2039_, v_m_2040_, v_a_2041_);
lean_dec(v_a_2041_);
lean_dec_ref(v_m_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_2043_, lean_object* v_x_2044_, lean_object* v_x_2045_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(v_x_2044_, v_x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
uint8_t v_res_2050_; lean_object* v_r_2051_; 
v_res_2050_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6(v_00_u03b2_2047_, v_x_2048_, v_x_2049_);
lean_dec_ref(v_x_2049_);
lean_dec_ref(v_x_2048_);
v_r_2051_ = lean_box(v_res_2050_);
return v_r_2051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_2052_, lean_object* v_a_2053_, lean_object* v_x_2054_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(v_a_2053_, v_x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2056_, lean_object* v_a_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9(v_00_u03b2_2056_, v_a_2057_, v_x_2058_);
lean_dec(v_x_2058_);
lean_dec(v_a_2057_);
return v_res_2059_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_2060_, lean_object* v_x_2061_, size_t v_x_2062_, lean_object* v_x_2063_){
_start:
{
uint8_t v___x_2064_; 
v___x_2064_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(v_x_2061_, v_x_2062_, v_x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2065_, lean_object* v_x_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
size_t v_x_11428__boxed_2069_; uint8_t v_res_2070_; lean_object* v_r_2071_; 
v_x_11428__boxed_2069_ = lean_unbox_usize(v_x_2067_);
lean_dec(v_x_2067_);
v_res_2070_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10(v_00_u03b2_2065_, v_x_2066_, v_x_11428__boxed_2069_, v_x_2068_);
lean_dec_ref(v_x_2068_);
lean_dec_ref(v_x_2066_);
v_r_2071_ = lean_box(v_res_2070_);
return v_r_2071_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13(lean_object* v_00_u03b2_2072_, lean_object* v_keys_2073_, lean_object* v_vals_2074_, lean_object* v_heq_2075_, lean_object* v_i_2076_, lean_object* v_k_2077_){
_start:
{
uint8_t v___x_2078_; 
v___x_2078_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(v_keys_2073_, v_i_2076_, v_k_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___boxed(lean_object* v_00_u03b2_2079_, lean_object* v_keys_2080_, lean_object* v_vals_2081_, lean_object* v_heq_2082_, lean_object* v_i_2083_, lean_object* v_k_2084_){
_start:
{
uint8_t v_res_2085_; lean_object* v_r_2086_; 
v_res_2085_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13(v_00_u03b2_2079_, v_keys_2080_, v_vals_2081_, v_heq_2082_, v_i_2083_, v_k_2084_);
lean_dec_ref(v_k_2084_);
lean_dec_ref(v_vals_2081_);
lean_dec_ref(v_keys_2080_);
v_r_2086_ = lean_box(v_res_2085_);
return v_r_2086_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__0));
v___x_2089_ = l_Lean_stringToMessageData(v___x_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix(lean_object* v_entry_2090_){
_start:
{
lean_object* v_text_x3f_2091_; 
v_text_x3f_2091_ = lean_ctor_get(v_entry_2090_, 1);
lean_inc(v_text_x3f_2091_);
lean_dec_ref(v_entry_2090_);
if (lean_obj_tag(v_text_x3f_2091_) == 0)
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9);
return v___x_2092_;
}
else
{
lean_object* v_val_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_val_2093_ = lean_ctor_get(v_text_x3f_2091_, 0);
lean_inc(v_val_2093_);
lean_dec_ref_known(v_text_x3f_2091_, 1);
v___x_2094_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1, &l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1_once, _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1);
v___x_2095_ = l_Lean_stringToMessageData(v_val_2093_);
v___x_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(lean_object* v_o_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v_env_2102_; lean_object* v___x_2103_; lean_object* v_toEnvExtension_2104_; lean_object* v_asyncMode_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v___x_2108_; lean_object* v_merged_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2117_; 
v___x_2100_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2101_ = lean_st_ref_get(v___y_2098_);
v_env_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc_ref(v_env_2102_);
lean_dec(v___x_2101_);
v___x_2103_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2104_ = lean_ctor_get(v___x_2103_, 0);
v_asyncMode_2105_ = lean_ctor_get(v_toEnvExtension_2104_, 2);
v___x_2106_ = lean_box(0);
v___x_2107_ = 0;
v___x_2108_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2100_, v___x_2103_, v_env_2102_, v_asyncMode_2105_, v___x_2106_, v___x_2107_);
v_merged_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v___x_2108_, 1);
lean_dec(v_unused_2118_);
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2117_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_merged_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2117_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v_merged_2109_);
lean_ctor_set(v___x_2111_, 0, v_o_2097_);
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_o_2097_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_merged_2109_);
v___x_2114_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; 
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg___boxed(lean_object* v_o_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(v_o_2119_, v___y_2120_);
lean_dec(v___y_2120_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2123_);
v___x_2127_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(v___x_2126_, v___y_2124_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0___boxed(lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2131_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4(lean_object* v_opts_2132_, lean_object* v_opt_2133_){
_start:
{
lean_object* v_name_2134_; lean_object* v_defValue_2135_; lean_object* v_map_2136_; lean_object* v___x_2137_; 
v_name_2134_ = lean_ctor_get(v_opt_2133_, 0);
v_defValue_2135_ = lean_ctor_get(v_opt_2133_, 1);
v_map_2136_ = lean_ctor_get(v_opts_2132_, 0);
v___x_2137_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2136_, v_name_2134_);
if (lean_obj_tag(v___x_2137_) == 0)
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_unbox(v_defValue_2135_);
return v___x_2138_;
}
else
{
lean_object* v_val_2139_; 
v_val_2139_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_val_2139_);
lean_dec_ref_known(v___x_2137_, 1);
if (lean_obj_tag(v_val_2139_) == 1)
{
uint8_t v_v_2140_; 
v_v_2140_ = lean_ctor_get_uint8(v_val_2139_, 0);
lean_dec_ref_known(v_val_2139_, 0);
return v_v_2140_;
}
else
{
uint8_t v___x_2141_; 
lean_dec(v_val_2139_);
v___x_2141_ = lean_unbox(v_defValue_2135_);
return v___x_2141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_2142_, lean_object* v_opt_2143_){
_start:
{
uint8_t v_res_2144_; lean_object* v_r_2145_; 
v_res_2144_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4(v_opts_2142_, v_opt_2143_);
lean_dec_ref(v_opt_2143_);
lean_dec_ref(v_opts_2142_);
v_r_2145_ = lean_box(v_res_2144_);
return v_r_2145_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_2152_, lean_object* v_x_2153_){
_start:
{
if (lean_obj_tag(v_x_2153_) == 1)
{
lean_object* v_pre_2154_; 
v_pre_2154_ = lean_ctor_get(v_x_2153_, 0);
switch(lean_obj_tag(v_pre_2154_))
{
case 1:
{
lean_object* v_pre_2155_; 
v_pre_2155_ = lean_ctor_get(v_pre_2154_, 0);
switch(lean_obj_tag(v_pre_2155_))
{
case 0:
{
lean_object* v_str_2156_; lean_object* v_str_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v_str_2156_ = lean_ctor_get(v_x_2153_, 1);
v_str_2157_ = lean_ctor_get(v_pre_2154_, 1);
v___x_2158_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_));
v___x_2159_ = lean_string_dec_eq(v_str_2157_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__0));
v___x_2161_ = lean_string_dec_eq(v_str_2157_, v___x_2160_);
if (v___x_2161_ == 0)
{
return v___x_2161_;
}
else
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__1));
v___x_2163_ = lean_string_dec_eq(v_str_2156_, v___x_2162_);
if (v___x_2163_ == 0)
{
return v___x_2163_;
}
else
{
return v_suppressElabErrors_2152_;
}
}
}
else
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__2));
v___x_2165_ = lean_string_dec_eq(v_str_2156_, v___x_2164_);
if (v___x_2165_ == 0)
{
return v___x_2165_;
}
else
{
return v_suppressElabErrors_2152_;
}
}
}
case 1:
{
lean_object* v_pre_2166_; 
v_pre_2166_ = lean_ctor_get(v_pre_2155_, 0);
if (lean_obj_tag(v_pre_2166_) == 0)
{
lean_object* v_str_2167_; lean_object* v_str_2168_; lean_object* v_str_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_str_2167_ = lean_ctor_get(v_x_2153_, 1);
v_str_2168_ = lean_ctor_get(v_pre_2154_, 1);
v_str_2169_ = lean_ctor_get(v_pre_2155_, 1);
v___x_2170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__3));
v___x_2171_ = lean_string_dec_eq(v_str_2169_, v___x_2170_);
if (v___x_2171_ == 0)
{
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__4));
v___x_2173_ = lean_string_dec_eq(v_str_2168_, v___x_2172_);
if (v___x_2173_ == 0)
{
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__5));
v___x_2175_ = lean_string_dec_eq(v_str_2167_, v___x_2174_);
if (v___x_2175_ == 0)
{
return v___x_2175_;
}
else
{
return v_suppressElabErrors_2152_;
}
}
}
}
else
{
uint8_t v___x_2176_; 
v___x_2176_ = 0;
return v___x_2176_;
}
}
default: 
{
uint8_t v___x_2177_; 
v___x_2177_ = 0;
return v___x_2177_;
}
}
}
case 0:
{
lean_object* v_str_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v_str_2178_ = lean_ctor_get(v_x_2153_, 1);
v___x_2179_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__0));
v___x_2180_ = lean_string_dec_eq(v_str_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
return v___x_2180_;
}
else
{
return v_suppressElabErrors_2152_;
}
}
default: 
{
uint8_t v___x_2181_; 
v___x_2181_ = 0;
return v___x_2181_;
}
}
}
else
{
uint8_t v___x_2182_; 
v___x_2182_ = 0;
return v___x_2182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_2183_, lean_object* v_x_2184_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2185_; uint8_t v_res_2186_; lean_object* v_r_2187_; 
v_suppressElabErrors_boxed_2185_ = lean_unbox(v_suppressElabErrors_2183_);
v_res_2186_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_2185_, v_x_2184_);
lean_dec(v_x_2184_);
v_r_2187_ = lean_box(v_res_2186_);
return v_r_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3(lean_object* v_ref_2188_, lean_object* v_msgData_2189_, uint8_t v_severity_2190_, uint8_t v_isSilent_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___y_2196_; uint8_t v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; uint8_t v___y_2201_; lean_object* v___y_2202_; lean_object* v_toCold_2203_; lean_object* v___y_2204_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; uint8_t v___y_2236_; uint8_t v___y_2237_; uint8_t v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2260_; lean_object* v___y_2261_; uint8_t v___y_2262_; uint8_t v___y_2263_; lean_object* v___y_2264_; uint8_t v___y_2265_; lean_object* v___y_2266_; uint8_t v___y_2270_; uint8_t v___y_2271_; uint8_t v___x_2281_; uint8_t v___y_2283_; uint8_t v___x_2289_; 
v___x_2281_ = 2;
v___x_2289_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2190_, v___x_2281_);
if (v___x_2289_ == 0)
{
v___y_2283_ = v___x_2289_;
goto v___jp_2282_;
}
else
{
uint8_t v___x_2290_; 
lean_inc_ref(v_msgData_2189_);
v___x_2290_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2189_);
if (v___x_2290_ == 0)
{
v___y_2283_ = v___x_2290_;
goto v___jp_2282_;
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec_ref(v_msgData_2189_);
v___x_2291_ = lean_box(0);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
return v___x_2292_;
}
}
v___jp_2195_:
{
lean_object* v_currNamespace_2205_; lean_object* v_openDecls_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v_env_2211_; lean_object* v_nextMacroScope_2212_; lean_object* v_ngen_2213_; lean_object* v_auxDeclNGen_2214_; lean_object* v_traceState_2215_; lean_object* v_cache_2216_; lean_object* v_recordedDeps_2217_; lean_object* v_messages_2218_; lean_object* v_infoState_2219_; lean_object* v_snapshotTasks_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2231_; 
v_currNamespace_2205_ = lean_ctor_get(v_toCold_2203_, 4);
v_openDecls_2206_ = lean_ctor_get(v_toCold_2203_, 5);
lean_inc(v_openDecls_2206_);
lean_inc(v_currNamespace_2205_);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v_currNamespace_2205_);
lean_ctor_set(v___x_2207_, 1, v_openDecls_2206_);
v___x_2208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___y_2202_);
lean_inc_ref(v___y_2200_);
lean_inc_ref(v___y_2198_);
v___x_2209_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2209_, 0, v___y_2198_);
lean_ctor_set(v___x_2209_, 1, v___y_2196_);
lean_ctor_set(v___x_2209_, 2, v___y_2199_);
lean_ctor_set(v___x_2209_, 3, v___y_2200_);
lean_ctor_set(v___x_2209_, 4, v___x_2208_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*5, v___y_2201_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*5 + 1, v___y_2197_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*5 + 2, v_isSilent_2191_);
v___x_2210_ = lean_st_ref_take(v___y_2204_);
v_env_2211_ = lean_ctor_get(v___x_2210_, 0);
v_nextMacroScope_2212_ = lean_ctor_get(v___x_2210_, 1);
v_ngen_2213_ = lean_ctor_get(v___x_2210_, 2);
v_auxDeclNGen_2214_ = lean_ctor_get(v___x_2210_, 3);
v_traceState_2215_ = lean_ctor_get(v___x_2210_, 4);
v_cache_2216_ = lean_ctor_get(v___x_2210_, 5);
v_recordedDeps_2217_ = lean_ctor_get(v___x_2210_, 6);
v_messages_2218_ = lean_ctor_get(v___x_2210_, 7);
v_infoState_2219_ = lean_ctor_get(v___x_2210_, 8);
v_snapshotTasks_2220_ = lean_ctor_get(v___x_2210_, 9);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2222_ = v___x_2210_;
v_isShared_2223_ = v_isSharedCheck_2231_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_snapshotTasks_2220_);
lean_inc(v_infoState_2219_);
lean_inc(v_messages_2218_);
lean_inc(v_recordedDeps_2217_);
lean_inc(v_cache_2216_);
lean_inc(v_traceState_2215_);
lean_inc(v_auxDeclNGen_2214_);
lean_inc(v_ngen_2213_);
lean_inc(v_nextMacroScope_2212_);
lean_inc(v_env_2211_);
lean_dec(v___x_2210_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2231_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = lean_box(0);
v___x_2225_ = l_Lean_MessageLog_add(v___x_2209_, v_messages_2218_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 7, v___x_2225_);
v___x_2227_ = v___x_2222_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_env_2211_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_nextMacroScope_2212_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_ngen_2213_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_auxDeclNGen_2214_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_traceState_2215_);
lean_ctor_set(v_reuseFailAlloc_2230_, 5, v_cache_2216_);
lean_ctor_set(v_reuseFailAlloc_2230_, 6, v_recordedDeps_2217_);
lean_ctor_set(v_reuseFailAlloc_2230_, 7, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2230_, 8, v_infoState_2219_);
lean_ctor_set(v_reuseFailAlloc_2230_, 9, v_snapshotTasks_2220_);
v___x_2227_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_st_ref_put(v___y_2204_, v___x_2227_);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2224_);
return v___x_2229_;
}
}
}
v___jp_2232_:
{
lean_object* v_fileName_2241_; lean_object* v_fileMap_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2258_; 
v_fileName_2241_ = lean_ctor_get(v___y_2235_, 0);
v_fileMap_2242_ = lean_ctor_get(v___y_2235_, 1);
v___x_2243_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2189_);
v___x_2244_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(v___x_2243_, v___y_2192_, v___y_2193_);
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2258_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2258_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_inc_ref_n(v_fileMap_2242_, 2);
v___x_2249_ = l_Lean_FileMap_toPosition(v_fileMap_2242_, v___y_2239_);
lean_dec(v___y_2239_);
v___x_2250_ = l_Lean_FileMap_toPosition(v_fileMap_2242_, v___y_2240_);
lean_dec(v___y_2240_);
v___x_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
v___x_2252_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1));
if (v___y_2237_ == 0)
{
lean_del_object(v___x_2247_);
lean_dec_ref(v___y_2234_);
v___y_2196_ = v___x_2249_;
v___y_2197_ = v___y_2236_;
v___y_2198_ = v_fileName_2241_;
v___y_2199_ = v___x_2251_;
v___y_2200_ = v___x_2252_;
v___y_2201_ = v___y_2238_;
v___y_2202_ = v_a_2245_;
v_toCold_2203_ = v___y_2233_;
v___y_2204_ = v___y_2193_;
goto v___jp_2195_;
}
else
{
uint8_t v___x_2253_; 
lean_inc(v_a_2245_);
v___x_2253_ = l_Lean_MessageData_hasTag(v___y_2234_, v_a_2245_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
lean_dec_ref_known(v___x_2251_, 1);
lean_dec_ref(v___x_2249_);
lean_dec(v_a_2245_);
v___x_2254_ = lean_box(0);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2254_);
v___x_2256_ = v___x_2247_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
else
{
lean_del_object(v___x_2247_);
v___y_2196_ = v___x_2249_;
v___y_2197_ = v___y_2236_;
v___y_2198_ = v_fileName_2241_;
v___y_2199_ = v___x_2251_;
v___y_2200_ = v___x_2252_;
v___y_2201_ = v___y_2238_;
v___y_2202_ = v_a_2245_;
v_toCold_2203_ = v___y_2233_;
v___y_2204_ = v___y_2193_;
goto v___jp_2195_;
}
}
}
}
v___jp_2259_:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Syntax_getTailPos_x3f(v___y_2264_, v___y_2265_);
lean_dec(v___y_2264_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_inc(v___y_2266_);
v___y_2233_ = v___y_2260_;
v___y_2234_ = v___y_2261_;
v___y_2235_ = v___y_2260_;
v___y_2236_ = v___y_2263_;
v___y_2237_ = v___y_2262_;
v___y_2238_ = v___y_2265_;
v___y_2239_ = v___y_2266_;
v___y_2240_ = v___y_2266_;
goto v___jp_2232_;
}
else
{
lean_object* v_val_2268_; 
v_val_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_val_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___y_2233_ = v___y_2260_;
v___y_2234_ = v___y_2261_;
v___y_2235_ = v___y_2260_;
v___y_2236_ = v___y_2263_;
v___y_2237_ = v___y_2262_;
v___y_2238_ = v___y_2265_;
v___y_2239_ = v___y_2266_;
v___y_2240_ = v_val_2268_;
goto v___jp_2232_;
}
}
v___jp_2269_:
{
lean_object* v_toCold_2272_; lean_object* v_ref_2273_; uint8_t v_suppressElabErrors_2274_; lean_object* v___x_2275_; lean_object* v___f_2276_; lean_object* v_ref_2277_; lean_object* v___x_2278_; 
v_toCold_2272_ = lean_ctor_get(v___y_2192_, 0);
v_ref_2273_ = lean_ctor_get(v___y_2192_, 2);
v_suppressElabErrors_2274_ = lean_ctor_get_uint8(v___y_2192_, sizeof(void*)*3 + 2);
v___x_2275_ = lean_box(v_suppressElabErrors_2274_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2276_, 0, v___x_2275_);
v_ref_2277_ = l_Lean_replaceRef(v_ref_2188_, v_ref_2273_);
v___x_2278_ = l_Lean_Syntax_getPos_x3f(v_ref_2277_, v___y_2270_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_unsigned_to_nat(0u);
v___y_2260_ = v_toCold_2272_;
v___y_2261_ = v___f_2276_;
v___y_2262_ = v_suppressElabErrors_2274_;
v___y_2263_ = v___y_2271_;
v___y_2264_ = v_ref_2277_;
v___y_2265_ = v___y_2270_;
v___y_2266_ = v___x_2279_;
goto v___jp_2259_;
}
else
{
lean_object* v_val_2280_; 
v_val_2280_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_val_2280_);
lean_dec_ref_known(v___x_2278_, 1);
v___y_2260_ = v_toCold_2272_;
v___y_2261_ = v___f_2276_;
v___y_2262_ = v_suppressElabErrors_2274_;
v___y_2263_ = v___y_2271_;
v___y_2264_ = v_ref_2277_;
v___y_2265_ = v___y_2270_;
v___y_2266_ = v_val_2280_;
goto v___jp_2259_;
}
}
v___jp_2282_:
{
uint8_t v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = 1;
v___x_2285_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2190_, v___x_2284_);
if (v___x_2285_ == 0)
{
v___y_2270_ = v___y_2283_;
v___y_2271_ = v_severity_2190_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2286_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2192_);
v___x_2287_ = l_Lean_warningAsError;
v___x_2288_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4(v___x_2286_, v___x_2287_);
lean_dec_ref(v___x_2286_);
if (v___x_2288_ == 0)
{
v___y_2270_ = v___y_2283_;
v___y_2271_ = v_severity_2190_;
goto v___jp_2269_;
}
else
{
v___y_2270_ = v___y_2283_;
v___y_2271_ = v___x_2281_;
goto v___jp_2269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_2293_, lean_object* v_msgData_2294_, lean_object* v_severity_2295_, lean_object* v_isSilent_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
uint8_t v_severity_boxed_2300_; uint8_t v_isSilent_boxed_2301_; lean_object* v_res_2302_; 
v_severity_boxed_2300_ = lean_unbox(v_severity_2295_);
v_isSilent_boxed_2301_ = lean_unbox(v_isSilent_2296_);
v_res_2302_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3(v_ref_2293_, v_msgData_2294_, v_severity_boxed_2300_, v_isSilent_boxed_2301_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v_ref_2293_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2(lean_object* v_ref_2303_, lean_object* v_msgData_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
uint8_t v___x_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = 1;
v___x_2309_ = 0;
v___x_2310_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3(v_ref_2303_, v_msgData_2304_, v___x_2308_, v___x_2309_, v___y_2305_, v___y_2306_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2___boxed(lean_object* v_ref_2311_, lean_object* v_msgData_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2(v_ref_2311_, v_msgData_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v_ref_2311_);
return v_res_2316_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__0));
v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__2));
v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(lean_object* v_linterOption_2323_, lean_object* v_stx_2324_, lean_object* v_msg_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_name_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2347_; 
v_name_2329_ = lean_ctor_get(v_linterOption_2323_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_linterOption_2323_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v_linterOption_2323_, 1);
lean_dec(v_unused_2348_);
v___x_2331_ = v_linterOption_2323_;
v_isShared_2332_ = v_isSharedCheck_2347_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_name_2329_);
lean_dec(v_linterOption_2323_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2347_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2333_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1);
lean_inc(v_name_2329_);
v___x_2334_ = l_Lean_MessageData_ofName(v_name_2329_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set_tag(v___x_2331_, 7);
lean_ctor_set(v___x_2331_, 1, v___x_2334_);
lean_ctor_set(v___x_2331_, 0, v___x_2333_);
v___x_2336_ = v___x_2331_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v_disable_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2337_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3);
v___x_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2336_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v_disable_2339_ = l_Lean_MessageData_note(v___x_2338_);
v___x_2340_ = l_Lean_Linter_linterMessageTag;
v___x_2341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2341_, 0, v_msg_2325_);
lean_ctor_set(v___x_2341_, 1, v_disable_2339_);
v___x_2342_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2343_, 0, v_name_2329_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
lean_inc(v_stx_2324_);
v___x_2344_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2344_, 0, v_stx_2324_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2(v_stx_2324_, v___x_2344_, v___y_2326_, v___y_2327_);
lean_dec(v_stx_2324_);
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___boxed(lean_object* v_linterOption_2349_, lean_object* v_stx_2350_, lean_object* v_msg_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v_linterOption_2349_, v_stx_2350_, v_msg_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
return v_res_2355_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__1(void){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__0));
v___x_2358_ = l_Lean_stringToMessageData(v___x_2357_);
return v___x_2358_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__3(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__2));
v___x_2361_ = l_Lean_stringToMessageData(v___x_2360_);
return v___x_2361_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__5(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__4));
v___x_2364_ = l_Lean_stringToMessageData(v___x_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__7(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__6));
v___x_2367_ = l_Lean_stringToMessageData(v___x_2366_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__8));
v___x_2370_ = l_Lean_stringToMessageData(v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__11(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__10));
v___x_2373_ = l_Lean_stringToMessageData(v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__13(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__12));
v___x_2376_ = l_Lean_stringToMessageData(v___x_2375_);
return v___x_2376_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__15(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__14));
v___x_2379_ = l_Lean_stringToMessageData(v___x_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax(lean_object* v_stx_2380_, lean_object* v_macroStack_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v_env_2387_; lean_object* v___x_2388_; lean_object* v_toEnvExtension_2389_; lean_object* v_asyncMode_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2385_ = lean_box(1);
v___x_2386_ = lean_st_ref_get(v_a_2383_);
v_env_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc_ref(v_env_2387_);
lean_dec(v___x_2386_);
v___x_2388_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_2389_ = lean_ctor_get(v___x_2388_, 0);
v_asyncMode_2390_ = lean_ctor_get(v_toEnvExtension_2389_, 2);
lean_inc(v_stx_2380_);
v___x_2391_ = l_Lean_Syntax_getKind(v_stx_2380_);
v___x_2392_ = lean_box(0);
v___x_2393_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2385_, v___x_2388_, v_env_2387_, v_asyncMode_2390_, v___x_2392_);
v___x_2394_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2393_, v___x_2391_);
lean_dec(v___x_2393_);
if (lean_obj_tag(v___x_2394_) == 1)
{
lean_object* v_val_2395_; lean_object* v___x_2396_; lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2540_; 
v_val_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_val_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2396_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(v_a_2382_, v_a_2383_);
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2540_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2540_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_2402_ = l_Lean_Linter_getLinterValue(v___x_2401_, v_a_2397_);
lean_dec(v_a_2397_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
lean_dec(v_val_2395_);
lean_dec(v___x_2391_);
lean_dec(v_macroStack_2381_);
lean_dec(v_stx_2380_);
v___x_2403_ = lean_box(0);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2403_);
v___x_2405_ = v___x_2399_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
else
{
lean_object* v___x_2407_; 
lean_del_object(v___x_2399_);
v___x_2407_ = l_Lean_Core_shouldCheckDeprecated___redArg(v_stx_2380_, v_a_2382_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2531_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2531_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2531_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
uint8_t v___x_2412_; 
v___x_2412_ = lean_unbox(v_a_2408_);
lean_dec(v_a_2408_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
lean_dec(v_val_2395_);
lean_dec(v___x_2391_);
lean_dec(v_macroStack_2381_);
lean_dec(v_stx_2380_);
v___x_2413_ = lean_box(0);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2413_);
v___x_2415_ = v___x_2410_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_del_object(v___x_2410_);
v___x_2417_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix(v_val_2395_);
v___x_2418_ = l_Lean_Syntax_getHeadInfo(v_stx_2380_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v___x_2419_; 
lean_dec_ref_known(v___x_2418_, 4);
lean_dec(v_macroStack_2381_);
lean_inc(v_stx_2380_);
v___x_2419_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(v_stx_2380_, v_a_2382_, v_a_2383_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v___x_2421_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__1);
v___x_2422_ = l_Lean_MessageData_ofName(v___x_2391_);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__3);
v___x_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2423_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set(v___x_2426_, 1, v___x_2417_);
v___x_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v_a_2420_);
v___x_2428_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2401_, v_stx_2380_, v___x_2427_, v_a_2382_, v_a_2383_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2436_; 
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2436_ == 0)
{
lean_object* v_unused_2437_; 
v_unused_2437_ = lean_ctor_get(v___x_2428_, 0);
lean_dec(v_unused_2437_);
v___x_2430_ = v___x_2428_;
v_isShared_2431_ = v_isSharedCheck_2436_;
goto v_resetjp_2429_;
}
else
{
lean_dec(v___x_2428_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2436_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2432_ = lean_box(0);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2432_);
v___x_2434_ = v___x_2430_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
else
{
return v___x_2428_;
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec_ref(v___x_2417_);
lean_dec(v___x_2391_);
lean_dec(v_stx_2380_);
v_a_2438_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2419_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2419_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
else
{
lean_dec(v___x_2418_);
if (lean_obj_tag(v_macroStack_2381_) == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2446_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__1);
v___x_2447_ = l_Lean_MessageData_ofName(v___x_2391_);
v___x_2448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__3);
v___x_2450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2450_);
lean_ctor_set(v___x_2451_, 1, v___x_2417_);
v___x_2452_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2401_, v_stx_2380_, v___x_2451_, v_a_2382_, v_a_2383_);
return v___x_2452_;
}
else
{
lean_object* v_head_2453_; lean_object* v_tail_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_stx_2380_);
v_head_2453_ = lean_ctor_get(v_macroStack_2381_, 0);
v_tail_2454_ = lean_ctor_get(v_macroStack_2381_, 1);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_macroStack_2381_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2456_ = v_macroStack_2381_;
v_isShared_2457_ = v_isSharedCheck_2530_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_tail_2454_);
lean_inc(v_head_2453_);
lean_dec(v_macroStack_2381_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2530_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
if (lean_obj_tag(v_tail_2454_) == 0)
{
lean_object* v_before_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2478_; 
v_before_2458_ = lean_ctor_get(v_head_2453_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_head_2453_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v_head_2453_, 1);
lean_dec(v_unused_2479_);
v___x_2460_ = v_head_2453_;
v_isShared_2461_ = v_isSharedCheck_2478_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_before_2458_);
lean_dec(v_head_2453_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2478_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2462_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__5, &l_Lean_Elab_checkDeprecatedSyntax___closed__5_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__5);
lean_inc(v_before_2458_);
v___x_2463_ = l_Lean_Syntax_getKind(v_before_2458_);
v___x_2464_ = l_Lean_MessageData_ofName(v___x_2463_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set_tag(v___x_2460_, 7);
lean_ctor_set(v___x_2460_, 1, v___x_2464_);
lean_ctor_set(v___x_2460_, 0, v___x_2462_);
v___x_2466_ = v___x_2460_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__7, &l_Lean_Elab_checkDeprecatedSyntax___closed__7_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__7);
if (v_isShared_2457_ == 0)
{
lean_ctor_set_tag(v___x_2456_, 7);
lean_ctor_set(v___x_2456_, 1, v___x_2467_);
lean_ctor_set(v___x_2456_, 0, v___x_2466_);
v___x_2469_ = v___x_2456_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2470_ = l_Lean_MessageData_ofName(v___x_2391_);
v___x_2471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9);
v___x_2473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
lean_ctor_set(v___x_2474_, 1, v___x_2417_);
v___x_2475_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2401_, v_before_2458_, v___x_2474_, v_a_2382_, v_a_2383_);
return v___x_2475_;
}
}
}
}
else
{
lean_object* v_head_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2528_; 
v_head_2480_ = lean_ctor_get(v_tail_2454_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_tail_2454_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v_tail_2454_, 1);
lean_dec(v_unused_2529_);
v___x_2482_ = v_tail_2454_;
v_isShared_2483_ = v_isSharedCheck_2528_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_head_2480_);
lean_dec(v_tail_2454_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2528_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v_before_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2526_; 
v_before_2484_ = lean_ctor_get(v_head_2453_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_head_2453_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v_head_2453_, 1);
lean_dec(v_unused_2527_);
v___x_2486_ = v_head_2453_;
v_isShared_2487_ = v_isSharedCheck_2526_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_before_2484_);
lean_dec(v_head_2453_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2526_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v_before_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2524_; 
v_before_2488_ = lean_ctor_get(v_head_2480_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_head_2480_);
if (v_isSharedCheck_2524_ == 0)
{
lean_object* v_unused_2525_; 
v_unused_2525_ = lean_ctor_get(v_head_2480_, 1);
lean_dec(v_unused_2525_);
v___x_2490_ = v_head_2480_;
v_isShared_2491_ = v_isSharedCheck_2524_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_before_2488_);
lean_dec(v_head_2480_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2524_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___y_2495_; uint8_t v___x_2517_; 
v___x_2492_ = l_Lean_Syntax_getKind(v_before_2488_);
lean_inc(v_before_2484_);
v___x_2493_ = l_Lean_Syntax_getKind(v_before_2484_);
v___x_2517_ = lean_name_eq(v___x_2492_, v___x_2493_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2518_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__13, &l_Lean_Elab_checkDeprecatedSyntax___closed__13_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__13);
v___x_2519_ = l_Lean_MessageData_ofName(v___x_2492_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__15, &l_Lean_Elab_checkDeprecatedSyntax___closed__15_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__15);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___y_2495_ = v___x_2522_;
goto v___jp_2494_;
}
else
{
lean_object* v___x_2523_; 
lean_dec(v___x_2492_);
v___x_2523_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9);
v___y_2495_ = v___x_2523_;
goto v___jp_2494_;
}
v___jp_2494_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2496_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__5, &l_Lean_Elab_checkDeprecatedSyntax___closed__5_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__5);
v___x_2497_ = l_Lean_MessageData_ofName(v___x_2493_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set_tag(v___x_2490_, 7);
lean_ctor_set(v___x_2490_, 1, v___x_2497_);
lean_ctor_set(v___x_2490_, 0, v___x_2496_);
v___x_2499_ = v___x_2490_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2500_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9);
if (v_isShared_2483_ == 0)
{
lean_ctor_set_tag(v___x_2482_, 7);
lean_ctor_set(v___x_2482_, 1, v___x_2500_);
lean_ctor_set(v___x_2482_, 0, v___x_2499_);
v___x_2502_ = v___x_2482_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2504_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set_tag(v___x_2486_, 7);
lean_ctor_set(v___x_2486_, 1, v___y_2495_);
lean_ctor_set(v___x_2486_, 0, v___x_2502_);
v___x_2504_ = v___x_2486_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___y_2495_);
v___x_2504_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2505_; lean_object* v___x_2507_; 
v___x_2505_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__11, &l_Lean_Elab_checkDeprecatedSyntax___closed__11_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__11);
if (v_isShared_2457_ == 0)
{
lean_ctor_set_tag(v___x_2456_, 7);
lean_ctor_set(v___x_2456_, 1, v___x_2505_);
lean_ctor_set(v___x_2456_, 0, v___x_2504_);
v___x_2507_ = v___x_2456_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2508_ = l_Lean_MessageData_ofName(v___x_2391_);
v___x_2509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___x_2500_);
v___x_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2417_);
v___x_2512_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2401_, v_before_2484_, v___x_2511_, v_a_2382_, v_a_2383_);
return v___x_2512_;
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
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec(v_val_2395_);
lean_dec(v___x_2391_);
lean_dec(v_macroStack_2381_);
lean_dec(v_stx_2380_);
v_a_2532_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2407_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2407_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec(v___x_2394_);
lean_dec(v___x_2391_);
lean_dec(v_macroStack_2381_);
lean_dec(v_stx_2380_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___boxed(lean_object* v_stx_2543_, lean_object* v_macroStack_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Elab_checkDeprecatedSyntax(v_stx_2543_, v_macroStack_2544_, v_a_2545_, v_a_2546_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0(lean_object* v_o_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(v_o_2549_, v___y_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___boxed(lean_object* v_o_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0(v_o_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
return v_res_2558_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__0));
v___x_2561_ = l_Lean_stringToMessageData(v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax(lean_object* v_stx_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v_env_2568_; lean_object* v___x_2569_; lean_object* v_toEnvExtension_2570_; lean_object* v_asyncMode_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2566_ = lean_box(1);
v___x_2567_ = lean_st_ref_get(v_a_2564_);
v_env_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_ref(v_env_2568_);
lean_dec(v___x_2567_);
v___x_2569_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_2570_ = lean_ctor_get(v___x_2569_, 0);
v_asyncMode_2571_ = lean_ctor_get(v_toEnvExtension_2570_, 2);
v___x_2572_ = lean_box(0);
v___x_2573_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2566_, v___x_2569_, v_env_2568_, v_asyncMode_2571_, v___x_2572_);
lean_inc(v_stx_2562_);
v___x_2574_ = l_Lean_Syntax_getKind(v_stx_2562_);
v___x_2575_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2573_, v___x_2574_);
lean_dec(v___x_2573_);
if (lean_obj_tag(v___x_2575_) == 1)
{
lean_object* v_val_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2635_; 
v_val_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2635_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_val_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2635_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_Syntax_getHeadInfo(v_stx_2562_);
if (lean_obj_tag(v___x_2580_) == 1)
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
lean_dec_ref_known(v___x_2580_, 2);
lean_dec(v_val_2576_);
lean_dec(v___x_2574_);
lean_dec(v_stx_2562_);
v___x_2581_ = lean_box(0);
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2581_);
v___x_2583_ = v___x_2578_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
else
{
lean_object* v___x_2585_; lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v___x_2580_);
lean_del_object(v___x_2578_);
v___x_2585_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(v_a_2563_, v_a_2564_);
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2634_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2634_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; uint8_t v___x_2591_; 
v___x_2590_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_2591_ = l_Lean_Linter_getLinterValue(v___x_2590_, v_a_2586_);
lean_dec(v_a_2586_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2594_; 
lean_dec(v_val_2576_);
lean_dec(v___x_2574_);
lean_dec(v_stx_2562_);
v___x_2592_ = lean_box(0);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2592_);
v___x_2594_ = v___x_2588_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
else
{
lean_object* v___x_2596_; 
lean_del_object(v___x_2588_);
v___x_2596_ = l_Lean_Core_shouldCheckDeprecated___redArg(v_stx_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2625_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2625_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2625_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
uint8_t v___x_2601_; 
v___x_2601_ = lean_unbox(v_a_2597_);
lean_dec(v_a_2597_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2604_; 
lean_dec(v_val_2576_);
lean_dec(v___x_2574_);
lean_dec(v_stx_2562_);
v___x_2602_ = lean_box(0);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2602_);
v___x_2604_ = v___x_2599_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
else
{
lean_object* v___x_2606_; 
lean_del_object(v___x_2599_);
lean_inc(v_stx_2562_);
v___x_2606_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(v_stx_2562_, v_a_2563_, v_a_2564_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1, &l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1_once, _init_l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1);
v___x_2609_ = l_Lean_MessageData_ofName(v___x_2574_);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9);
v___x_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2610_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix(v_val_2576_);
v___x_2614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v_a_2607_);
v___x_2616_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2590_, v_stx_2562_, v___x_2615_, v_a_2563_, v_a_2564_);
return v___x_2616_;
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v_val_2576_);
lean_dec(v___x_2574_);
lean_dec(v_stx_2562_);
v_a_2617_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2606_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2606_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v_val_2576_);
lean_dec(v___x_2574_);
lean_dec(v_stx_2562_);
v_a_2626_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2596_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2596_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
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
lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_dec(v___x_2575_);
lean_dec(v___x_2574_);
lean_dec(v_stx_2562_);
v___x_2636_ = lean_box(0);
v___x_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
return v___x_2637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax___boxed(lean_object* v_stx_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_Elab_checkDeprecatedQuotedSyntax(v_stx_2638_, v_a_2639_, v_a_2640_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
return v_res_2642_;
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
