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
uint8_t v___x_9984__boxed_1108_; uint8_t v_res_1109_; lean_object* v_r_1110_; 
v___x_9984__boxed_1108_ = lean_unbox(v___x_1106_);
v_res_1109_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0(v___x_9984__boxed_1108_, v_s_1107_);
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
lean_object* v_toCold_1192_; lean_object* v_currRecDepth_1193_; lean_object* v_ref_1194_; uint16_t v_optionFlags_1195_; uint8_t v_suppressElabErrors_1196_; uint8_t v_isRecordingDeps_1197_; lean_object* v_ref_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_toCold_1192_ = lean_ctor_get(v___y_1189_, 0);
v_currRecDepth_1193_ = lean_ctor_get(v___y_1189_, 1);
v_ref_1194_ = lean_ctor_get(v___y_1189_, 2);
v_optionFlags_1195_ = lean_ctor_get_uint16(v___y_1189_, sizeof(void*)*3);
v_suppressElabErrors_1196_ = lean_ctor_get_uint8(v___y_1189_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1197_ = lean_ctor_get_uint8(v___y_1189_, sizeof(void*)*3 + 3);
v_ref_1198_ = l_Lean_replaceRef(v_ref_1187_, v_ref_1194_);
lean_inc(v_currRecDepth_1193_);
lean_inc_ref(v_toCold_1192_);
v___x_1199_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1199_, 0, v_toCold_1192_);
lean_ctor_set(v___x_1199_, 1, v_currRecDepth_1193_);
lean_ctor_set(v___x_1199_, 2, v_ref_1198_);
lean_ctor_set_uint16(v___x_1199_, sizeof(void*)*3, v_optionFlags_1195_);
lean_ctor_set_uint8(v___x_1199_, sizeof(void*)*3 + 2, v_suppressElabErrors_1196_);
lean_ctor_set_uint8(v___x_1199_, sizeof(void*)*3 + 3, v_isRecordingDeps_1197_);
v___x_1200_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1___redArg(v_msg_1188_, v___x_1199_, v___y_1190_);
lean_dec_ref_known(v___x_1199_, 3);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1201_, lean_object* v_msg_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(v_ref_1201_, v_msg_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v_ref_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4(lean_object* v_env_1207_, lean_object* v_currNamespace_1208_, lean_object* v_openDecls_1209_, lean_object* v_n_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = l_Lean_ResolveName_resolveNamespace(v_env_1207_, v_currNamespace_1208_, v_openDecls_1209_, v_n_1210_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v___y_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4___boxed(lean_object* v_env_1215_, lean_object* v_currNamespace_1216_, lean_object* v_openDecls_1217_, lean_object* v_n_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4(v_env_1215_, v_currNamespace_1216_, v_openDecls_1217_, v_n_1218_, v___y_1219_, v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3(lean_object* v_env_1222_, lean_object* v___x_1223_, lean_object* v_currNamespace_1224_, lean_object* v_openDecls_1225_, lean_object* v_n_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = l_Lean_ResolveName_resolveGlobalName(v_env_1222_, v___x_1223_, v_currNamespace_1224_, v_openDecls_1225_, v_n_1226_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___y_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3___boxed(lean_object* v_env_1231_, lean_object* v___x_1232_, lean_object* v_currNamespace_1233_, lean_object* v_openDecls_1234_, lean_object* v_n_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3(v_env_1231_, v___x_1232_, v_currNamespace_1233_, v_openDecls_1234_, v_n_1235_, v___y_1236_, v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v___x_1232_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2(lean_object* v_currNamespace_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v_currNamespace_1239_);
lean_ctor_set(v___x_1242_, 1, v___y_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2___boxed(lean_object* v_currNamespace_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2(v_currNamespace_1243_, v___y_1244_, v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1246_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = l_Lean_maxRecDepthErrorMessage;
v___x_1253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__3);
v___x_1255_ = l_Lean_MessageData_ofFormat(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__4);
v___x_1257_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__2));
v___x_1258_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v___x_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(lean_object* v_ref_1259_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___closed__5);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_ref_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(v_ref_1264_);
return v_res_1266_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1267_; double v___x_1268_; 
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_float_of_nat(v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(lean_object* v_cls_1272_, lean_object* v_msg_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_ref_1277_; lean_object* v___x_1278_; lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1324_; 
v_ref_1277_ = lean_ctor_get(v___y_1274_, 2);
v___x_1278_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(v_msg_1273_, v___y_1274_, v___y_1275_);
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1324_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1324_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v_traceState_1284_; lean_object* v_env_1285_; lean_object* v_nextMacroScope_1286_; lean_object* v_ngen_1287_; lean_object* v_auxDeclNGen_1288_; lean_object* v_cache_1289_; lean_object* v_recordedDeps_1290_; lean_object* v_messages_1291_; lean_object* v_infoState_1292_; lean_object* v_snapshotTasks_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1323_; 
v___x_1283_ = lean_st_ref_take(v___y_1275_);
v_traceState_1284_ = lean_ctor_get(v___x_1283_, 4);
v_env_1285_ = lean_ctor_get(v___x_1283_, 0);
v_nextMacroScope_1286_ = lean_ctor_get(v___x_1283_, 1);
v_ngen_1287_ = lean_ctor_get(v___x_1283_, 2);
v_auxDeclNGen_1288_ = lean_ctor_get(v___x_1283_, 3);
v_cache_1289_ = lean_ctor_get(v___x_1283_, 5);
v_recordedDeps_1290_ = lean_ctor_get(v___x_1283_, 6);
v_messages_1291_ = lean_ctor_get(v___x_1283_, 7);
v_infoState_1292_ = lean_ctor_get(v___x_1283_, 8);
v_snapshotTasks_1293_ = lean_ctor_get(v___x_1283_, 9);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1295_ = v___x_1283_;
v_isShared_1296_ = v_isSharedCheck_1323_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_snapshotTasks_1293_);
lean_inc(v_infoState_1292_);
lean_inc(v_messages_1291_);
lean_inc(v_recordedDeps_1290_);
lean_inc(v_cache_1289_);
lean_inc(v_traceState_1284_);
lean_inc(v_auxDeclNGen_1288_);
lean_inc(v_ngen_1287_);
lean_inc(v_nextMacroScope_1286_);
lean_inc(v_env_1285_);
lean_dec(v___x_1283_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1323_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
uint64_t v_tid_1297_; lean_object* v_traces_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1322_; 
v_tid_1297_ = lean_ctor_get_uint64(v_traceState_1284_, sizeof(void*)*1);
v_traces_1298_ = lean_ctor_get(v_traceState_1284_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_traceState_1284_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1300_ = v_traceState_1284_;
v_isShared_1301_ = v_isSharedCheck_1322_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_traces_1298_);
lean_dec(v_traceState_1284_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1322_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; double v___x_1304_; uint8_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__0);
v___x_1305_ = 0;
v___x_1306_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1));
v___x_1307_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1307_, 0, v_cls_1272_);
lean_ctor_set(v___x_1307_, 1, v___x_1303_);
lean_ctor_set(v___x_1307_, 2, v___x_1306_);
lean_ctor_set_float(v___x_1307_, sizeof(void*)*3, v___x_1304_);
lean_ctor_set_float(v___x_1307_, sizeof(void*)*3 + 8, v___x_1304_);
lean_ctor_set_uint8(v___x_1307_, sizeof(void*)*3 + 16, v___x_1305_);
v___x_1308_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__2));
v___x_1309_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v_a_1279_);
lean_ctor_set(v___x_1309_, 2, v___x_1308_);
lean_inc(v_ref_1277_);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_ref_1277_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = l_Lean_PersistentArray_push___redArg(v_traces_1298_, v___x_1310_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1311_);
v___x_1313_ = v___x_1300_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1311_);
lean_ctor_set_uint64(v_reuseFailAlloc_1321_, sizeof(void*)*1, v_tid_1297_);
v___x_1313_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1315_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 4, v___x_1313_);
v___x_1315_ = v___x_1295_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_env_1285_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_nextMacroScope_1286_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_ngen_1287_);
lean_ctor_set(v_reuseFailAlloc_1320_, 3, v_auxDeclNGen_1288_);
lean_ctor_set(v_reuseFailAlloc_1320_, 4, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1320_, 5, v_cache_1289_);
lean_ctor_set(v_reuseFailAlloc_1320_, 6, v_recordedDeps_1290_);
lean_ctor_set(v_reuseFailAlloc_1320_, 7, v_messages_1291_);
lean_ctor_set(v_reuseFailAlloc_1320_, 8, v_infoState_1292_);
lean_ctor_set(v_reuseFailAlloc_1320_, 9, v_snapshotTasks_1293_);
v___x_1315_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = lean_st_ref_put(v___y_1275_, v___x_1315_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1302_);
v___x_1318_ = v___x_1281_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1302_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___boxed(lean_object* v_cls_1325_, lean_object* v_msg_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(v_cls_1325_, v_msg_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4(lean_object* v_as_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
if (lean_obj_tag(v_as_1334_) == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
else
{
lean_object* v_toCold_1340_; lean_object* v_options_1341_; uint8_t v_hasTrace_1342_; 
v_toCold_1340_ = lean_ctor_get(v___y_1335_, 0);
v_options_1341_ = lean_ctor_get(v_toCold_1340_, 2);
v_hasTrace_1342_ = lean_ctor_get_uint8(v_options_1341_, sizeof(void*)*1);
if (v_hasTrace_1342_ == 0)
{
lean_object* v_tail_1343_; 
v_tail_1343_ = lean_ctor_get(v_as_1334_, 1);
lean_inc(v_tail_1343_);
lean_dec_ref_known(v_as_1334_, 2);
v_as_1334_ = v_tail_1343_;
goto _start;
}
else
{
lean_object* v_head_1345_; lean_object* v_tail_1346_; lean_object* v_fst_1347_; lean_object* v_snd_1348_; lean_object* v_inheritedTraceOptions_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_head_1345_ = lean_ctor_get(v_as_1334_, 0);
lean_inc(v_head_1345_);
v_tail_1346_ = lean_ctor_get(v_as_1334_, 1);
lean_inc(v_tail_1346_);
lean_dec_ref_known(v_as_1334_, 2);
v_fst_1347_ = lean_ctor_get(v_head_1345_, 0);
lean_inc_n(v_fst_1347_, 2);
v_snd_1348_ = lean_ctor_get(v_head_1345_, 1);
lean_inc(v_snd_1348_);
lean_dec(v_head_1345_);
v_inheritedTraceOptions_1349_ = lean_ctor_get(v_toCold_1340_, 11);
v___x_1350_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__1));
v___x_1351_ = l_Lean_Name_append(v___x_1350_, v_fst_1347_);
v___x_1352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1349_, v_options_1341_, v___x_1351_);
lean_dec(v___x_1351_);
if (v___x_1352_ == 0)
{
lean_dec(v_snd_1348_);
lean_dec(v_fst_1347_);
v_as_1334_ = v_tail_1346_;
goto _start;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_snd_1348_);
v___x_1355_ = l_Lean_MessageData_ofFormat(v___x_1354_);
v___x_1356_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(v_fst_1347_, v___x_1355_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_dec_ref_known(v___x_1356_, 1);
v_as_1334_ = v_tail_1346_;
goto _start;
}
else
{
lean_dec(v_tail_1346_);
return v___x_1356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___boxed(lean_object* v_as_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4(v_as_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1362_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(lean_object* v_keys_1363_, lean_object* v_i_1364_, lean_object* v_k_1365_){
_start:
{
lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = lean_array_get_size(v_keys_1363_);
v___x_1367_ = lean_nat_dec_lt(v_i_1364_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_dec(v_i_1364_);
return v___x_1367_;
}
else
{
lean_object* v_k_x27_1368_; uint8_t v___x_1369_; 
v_k_x27_1368_ = lean_array_fget_borrowed(v_keys_1363_, v_i_1364_);
v___x_1369_ = l_Lean_instBEqExtraModUse_beq(v_k_1365_, v_k_x27_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_add(v_i_1364_, v___x_1370_);
lean_dec(v_i_1364_);
v_i_1364_ = v___x_1371_;
goto _start;
}
else
{
lean_dec(v_i_1364_);
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg___boxed(lean_object* v_keys_1373_, lean_object* v_i_1374_, lean_object* v_k_1375_){
_start:
{
uint8_t v_res_1376_; lean_object* v_r_1377_; 
v_res_1376_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(v_keys_1373_, v_i_1374_, v_k_1375_);
lean_dec_ref(v_k_1375_);
lean_dec_ref(v_keys_1373_);
v_r_1377_ = lean_box(v_res_1376_);
return v_r_1377_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(lean_object* v_x_1378_, size_t v_x_1379_, lean_object* v_x_1380_){
_start:
{
if (lean_obj_tag(v_x_1378_) == 0)
{
lean_object* v_es_1381_; lean_object* v___x_1382_; size_t v___x_1383_; size_t v___x_1384_; lean_object* v_j_1385_; lean_object* v___x_1386_; 
v_es_1381_ = lean_ctor_get(v_x_1378_, 0);
v___x_1382_ = lean_box(2);
v___x_1383_ = ((size_t)31ULL);
v___x_1384_ = lean_usize_land(v_x_1379_, v___x_1383_);
v_j_1385_ = lean_usize_to_nat(v___x_1384_);
v___x_1386_ = lean_array_get_borrowed(v___x_1382_, v_es_1381_, v_j_1385_);
lean_dec(v_j_1385_);
switch(lean_obj_tag(v___x_1386_))
{
case 0:
{
lean_object* v_key_1387_; uint8_t v___x_1388_; 
v_key_1387_ = lean_ctor_get(v___x_1386_, 0);
v___x_1388_ = l_Lean_instBEqExtraModUse_beq(v_x_1380_, v_key_1387_);
return v___x_1388_;
}
case 1:
{
lean_object* v_node_1389_; size_t v___x_1390_; size_t v___x_1391_; 
v_node_1389_ = lean_ctor_get(v___x_1386_, 0);
v___x_1390_ = ((size_t)5ULL);
v___x_1391_ = lean_usize_shift_right(v_x_1379_, v___x_1390_);
v_x_1378_ = v_node_1389_;
v_x_1379_ = v___x_1391_;
goto _start;
}
default: 
{
uint8_t v___x_1393_; 
v___x_1393_ = 0;
return v___x_1393_;
}
}
}
else
{
lean_object* v_ks_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_ks_1394_ = lean_ctor_get(v_x_1378_, 0);
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(v_ks_1394_, v___x_1395_, v_x_1380_);
return v___x_1396_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
size_t v_x_10386__boxed_1400_; uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_x_10386__boxed_1400_ = lean_unbox_usize(v_x_1398_);
lean_dec(v_x_1398_);
v_res_1401_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(v_x_1397_, v_x_10386__boxed_1400_, v_x_1399_);
lean_dec_ref(v_x_1399_);
lean_dec_ref(v_x_1397_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(lean_object* v_x_1403_, lean_object* v_x_1404_){
_start:
{
uint64_t v___x_1405_; size_t v___x_1406_; uint8_t v___x_1407_; 
v___x_1405_ = l_Lean_instHashableExtraModUse_hash(v_x_1404_);
v___x_1406_ = lean_uint64_to_usize(v___x_1405_);
v___x_1407_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(v_x_1403_, v___x_1406_, v_x_1404_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_x_1408_, lean_object* v_x_1409_){
_start:
{
uint8_t v_res_1410_; lean_object* v_r_1411_; 
v_res_1410_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(v_x_1408_, v_x_1409_);
lean_dec_ref(v_x_1409_);
lean_dec_ref(v_x_1408_);
v_r_1411_ = lean_box(v_res_1410_);
return v_r_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___lam__0(lean_object* v___x_1412_, lean_object* v_entry_1413_, lean_object* v_s_1414_){
_start:
{
lean_object* v_addEntryFn_1415_; lean_object* v_importedEntries_1416_; lean_object* v_state_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1425_; 
v_addEntryFn_1415_ = lean_ctor_get(v___x_1412_, 3);
lean_inc(v_addEntryFn_1415_);
lean_dec_ref(v___x_1412_);
v_importedEntries_1416_ = lean_ctor_get(v_s_1414_, 0);
v_state_1417_ = lean_ctor_get(v_s_1414_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_s_1414_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1419_ = v_s_1414_;
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_state_1417_);
lean_inc(v_importedEntries_1416_);
lean_dec(v_s_1414_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1425_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_state_1421_; lean_object* v___x_1423_; 
v_state_1421_ = lean_apply_2(v_addEntryFn_1415_, v_state_1417_, v_entry_1413_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 1, v_state_1421_);
v___x_1423_ = v___x_1419_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_importedEntries_1416_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_state_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__0);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
return v___x_1429_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1430_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__5));
v___x_1436_ = l_Lean_stringToMessageData(v___x_1435_);
return v___x_1436_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__7));
v___x_1439_ = l_Lean_stringToMessageData(v___x_1438_);
return v___x_1439_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1));
v___x_1441_ = l_Lean_stringToMessageData(v___x_1440_);
return v___x_1441_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_cls_1442_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__4));
v___x_1443_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__1));
v___x_1444_ = l_Lean_Name_append(v___x_1443_, v_cls_1442_);
return v___x_1444_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__11));
v___x_1447_ = l_Lean_stringToMessageData(v___x_1446_);
return v___x_1447_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__13));
v___x_1450_ = l_Lean_stringToMessageData(v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(lean_object* v_mod_1455_, uint8_t v_isMeta_1456_, lean_object* v_hint_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_env_1479_; uint8_t v_isExporting_1480_; lean_object* v_entry_1481_; lean_object* v___x_1482_; lean_object* v_env_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1477_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__2);
v___x_1478_ = lean_st_ref_get(v___y_1459_);
v_env_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc_ref(v_env_1479_);
lean_dec(v___x_1478_);
v_isExporting_1480_ = lean_ctor_get_uint8(v_env_1479_, sizeof(void*)*13);
lean_dec_ref(v_env_1479_);
lean_inc(v_mod_1455_);
v_entry_1481_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1481_, 0, v_mod_1455_);
lean_ctor_set_uint8(v_entry_1481_, sizeof(void*)*1, v_isExporting_1480_);
lean_ctor_set_uint8(v_entry_1481_, sizeof(void*)*1 + 1, v_isMeta_1456_);
v___x_1482_ = lean_st_ref_get(v___y_1459_);
v_env_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc_ref(v_env_1483_);
lean_dec(v___x_1482_);
v___x_1484_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1485_ = lean_box(1);
v___x_1486_ = lean_box(0);
v___x_1487_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1477_, v___x_1484_, v_env_1483_, v___x_1485_, v___x_1486_);
v___x_1488_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(v___x_1487_, v_entry_1481_);
lean_dec(v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v_toCold_1489_; lean_object* v_options_1490_; lean_object* v_inheritedTraceOptions_1491_; uint8_t v_hasTrace_1492_; lean_object* v___f_1493_; uint8_t v___x_1494_; lean_object* v___y_1496_; 
v_toCold_1489_ = lean_ctor_get(v___y_1458_, 0);
v_options_1490_ = lean_ctor_get(v_toCold_1489_, 2);
v_inheritedTraceOptions_1491_ = lean_ctor_get(v_toCold_1489_, 11);
v_hasTrace_1492_ = lean_ctor_get_uint8(v_options_1490_, sizeof(void*)*1);
v___f_1493_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_1493_, 0, v___x_1484_);
lean_closure_set(v___f_1493_, 1, v_entry_1481_);
v___x_1494_ = 1;
if (v_hasTrace_1492_ == 0)
{
lean_dec(v_hint_1457_);
lean_dec(v_mod_1455_);
v___y_1496_ = v___y_1459_;
goto v___jp_1495_;
}
else
{
lean_object* v_cls_1514_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v_cls_1514_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__4));
v___x_1534_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__10);
v___x_1535_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1491_, v_options_1490_, v___x_1534_);
if (v___x_1535_ == 0)
{
lean_dec(v_hint_1457_);
lean_dec(v_mod_1455_);
v___y_1496_ = v___y_1459_;
goto v___jp_1495_;
}
else
{
lean_object* v___x_1536_; lean_object* v___y_1538_; 
v___x_1536_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__12);
if (v_isExporting_1480_ == 0)
{
lean_object* v___x_1545_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__17));
v___y_1538_ = v___x_1545_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1546_; 
v___x_1546_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__18));
v___y_1538_ = v___x_1546_;
goto v___jp_1537_;
}
v___jp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_inc_ref(v___y_1538_);
v___x_1539_ = l_Lean_stringToMessageData(v___y_1538_);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1536_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__14);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
if (v_isMeta_1456_ == 0)
{
lean_object* v___x_1543_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__15));
v___y_1521_ = v___x_1542_;
v___y_1522_ = v___x_1543_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1544_; 
v___x_1544_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__16));
v___y_1521_ = v___x_1542_;
v___y_1522_ = v___x_1544_;
goto v___jp_1520_;
}
}
}
v___jp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___y_1516_);
lean_ctor_set(v___x_1518_, 1, v___y_1517_);
v___x_1519_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0(v_cls_1514_, v___x_1518_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_dec_ref_known(v___x_1519_, 1);
v___y_1496_ = v___y_1459_;
goto v___jp_1495_;
}
else
{
lean_dec_ref(v___f_1493_);
return v___x_1519_;
}
}
v___jp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
lean_inc_ref(v___y_1522_);
v___x_1523_ = l_Lean_stringToMessageData(v___y_1522_);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___y_1521_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__6);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = l_Lean_MessageData_ofName(v_mod_1455_);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = l_Lean_Name_isAnonymous(v_hint_1457_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__8);
v___x_1531_ = l_Lean_MessageData_ofName(v_hint_1457_);
v___x_1532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___y_1516_ = v___x_1528_;
v___y_1517_ = v___x_1532_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1533_; 
lean_dec(v_hint_1457_);
v___x_1533_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9);
v___y_1516_ = v___x_1528_;
v___y_1517_ = v___x_1533_;
goto v___jp_1515_;
}
}
}
v___jp_1495_:
{
lean_object* v___x_1497_; lean_object* v_toEnvExtension_1498_; lean_object* v_env_1499_; lean_object* v_nextMacroScope_1500_; lean_object* v_ngen_1501_; lean_object* v_auxDeclNGen_1502_; lean_object* v_traceState_1503_; lean_object* v_recordedDeps_1504_; lean_object* v_messages_1505_; lean_object* v_infoState_1506_; lean_object* v_snapshotTasks_1507_; lean_object* v_asyncMode_1508_; uint8_t v_logWrites_1509_; lean_object* v___x_1510_; 
v___x_1497_ = lean_st_ref_take(v___y_1496_);
v_toEnvExtension_1498_ = lean_ctor_get(v___x_1484_, 0);
v_env_1499_ = lean_ctor_get(v___x_1497_, 0);
lean_inc_ref(v_env_1499_);
v_nextMacroScope_1500_ = lean_ctor_get(v___x_1497_, 1);
lean_inc(v_nextMacroScope_1500_);
v_ngen_1501_ = lean_ctor_get(v___x_1497_, 2);
lean_inc_ref(v_ngen_1501_);
v_auxDeclNGen_1502_ = lean_ctor_get(v___x_1497_, 3);
lean_inc_ref(v_auxDeclNGen_1502_);
v_traceState_1503_ = lean_ctor_get(v___x_1497_, 4);
lean_inc_ref(v_traceState_1503_);
v_recordedDeps_1504_ = lean_ctor_get(v___x_1497_, 6);
lean_inc_ref(v_recordedDeps_1504_);
v_messages_1505_ = lean_ctor_get(v___x_1497_, 7);
lean_inc_ref(v_messages_1505_);
v_infoState_1506_ = lean_ctor_get(v___x_1497_, 8);
lean_inc_ref(v_infoState_1506_);
v_snapshotTasks_1507_ = lean_ctor_get(v___x_1497_, 9);
lean_inc_ref(v_snapshotTasks_1507_);
lean_dec(v___x_1497_);
v_asyncMode_1508_ = lean_ctor_get(v_toEnvExtension_1498_, 2);
v_logWrites_1509_ = lean_ctor_get_uint8(v_toEnvExtension_1498_, sizeof(void*)*6);
v___x_1510_ = lean_box(0);
if (v_logWrites_1509_ == 0)
{
lean_object* v___x_1511_; 
lean_inc_ref(v_toEnvExtension_1498_);
v___x_1511_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1498_, v_env_1499_, v___f_1493_, v_asyncMode_1508_, v___x_1486_, v___x_1494_);
v___y_1462_ = v_nextMacroScope_1500_;
v___y_1463_ = v___x_1510_;
v___y_1464_ = v_snapshotTasks_1507_;
v___y_1465_ = v_traceState_1503_;
v___y_1466_ = v___y_1496_;
v___y_1467_ = v_messages_1505_;
v___y_1468_ = v_recordedDeps_1504_;
v___y_1469_ = v_infoState_1506_;
v___y_1470_ = v_auxDeclNGen_1502_;
v___y_1471_ = v_ngen_1501_;
v___y_1472_ = v___x_1511_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_inc_ref_n(v_toEnvExtension_1498_, 2);
v___x_1512_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1498_, v_env_1499_);
lean_dec_ref(v_env_1499_);
v___x_1513_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1498_, v___x_1512_, v___f_1493_, v_asyncMode_1508_, v___x_1486_, v___x_1494_);
v___y_1462_ = v_nextMacroScope_1500_;
v___y_1463_ = v___x_1510_;
v___y_1464_ = v_snapshotTasks_1507_;
v___y_1465_ = v_traceState_1503_;
v___y_1466_ = v___y_1496_;
v___y_1467_ = v_messages_1505_;
v___y_1468_ = v_recordedDeps_1504_;
v___y_1469_ = v_infoState_1506_;
v___y_1470_ = v_auxDeclNGen_1502_;
v___y_1471_ = v_ngen_1501_;
v___y_1472_ = v___x_1513_;
goto v___jp_1461_;
}
}
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec_ref_known(v_entry_1481_, 1);
lean_dec(v_hint_1457_);
lean_dec(v_mod_1455_);
v___x_1547_ = lean_box(0);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
v___jp_1461_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1473_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__1);
v___x_1474_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1474_, 0, v___y_1472_);
lean_ctor_set(v___x_1474_, 1, v___y_1462_);
lean_ctor_set(v___x_1474_, 2, v___y_1471_);
lean_ctor_set(v___x_1474_, 3, v___y_1470_);
lean_ctor_set(v___x_1474_, 4, v___y_1465_);
lean_ctor_set(v___x_1474_, 5, v___x_1473_);
lean_ctor_set(v___x_1474_, 6, v___y_1468_);
lean_ctor_set(v___x_1474_, 7, v___y_1467_);
lean_ctor_set(v___x_1474_, 8, v___y_1469_);
lean_ctor_set(v___x_1474_, 9, v___y_1464_);
v___x_1475_ = lean_st_ref_put(v___y_1466_, v___x_1474_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___y_1463_);
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___boxed(lean_object* v_mod_1549_, lean_object* v_isMeta_1550_, lean_object* v_hint_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
uint8_t v_isMeta_boxed_1555_; lean_object* v_res_1556_; 
v_isMeta_boxed_1555_ = lean_unbox(v_isMeta_1550_);
v_res_1556_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(v_mod_1549_, v_isMeta_boxed_1555_, v_hint_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(lean_object* v_a_1557_, lean_object* v_x_1558_){
_start:
{
if (lean_obj_tag(v_x_1558_) == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_box(0);
return v___x_1559_;
}
else
{
lean_object* v_key_1560_; lean_object* v_value_1561_; lean_object* v_tail_1562_; uint8_t v___x_1563_; 
v_key_1560_ = lean_ctor_get(v_x_1558_, 0);
v_value_1561_ = lean_ctor_get(v_x_1558_, 1);
v_tail_1562_ = lean_ctor_get(v_x_1558_, 2);
v___x_1563_ = lean_name_eq(v_key_1560_, v_a_1557_);
if (v___x_1563_ == 0)
{
v_x_1558_ = v_tail_1562_;
goto _start;
}
else
{
lean_object* v___x_1565_; 
lean_inc(v_value_1561_);
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v_value_1561_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_a_1566_, lean_object* v_x_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(v_a_1566_, v_x_1567_);
lean_dec(v_x_1567_);
lean_dec(v_a_1566_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(lean_object* v_m_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_buckets_1571_; lean_object* v___x_1572_; uint64_t v___y_1574_; 
v_buckets_1571_ = lean_ctor_get(v_m_1569_, 1);
v___x_1572_ = lean_array_get_size(v_buckets_1571_);
if (lean_obj_tag(v_a_1570_) == 0)
{
uint64_t v___x_1588_; 
v___x_1588_ = 1723ULL;
v___y_1574_ = v___x_1588_;
goto v___jp_1573_;
}
else
{
uint64_t v_hash_1589_; 
v_hash_1589_ = lean_ctor_get_uint64(v_a_1570_, sizeof(void*)*2);
v___y_1574_ = v_hash_1589_;
goto v___jp_1573_;
}
v___jp_1573_:
{
uint64_t v___x_1575_; uint64_t v___x_1576_; uint64_t v_fold_1577_; uint64_t v___x_1578_; uint64_t v___x_1579_; uint64_t v___x_1580_; size_t v___x_1581_; size_t v___x_1582_; size_t v___x_1583_; size_t v___x_1584_; size_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1575_ = 32ULL;
v___x_1576_ = lean_uint64_shift_right(v___y_1574_, v___x_1575_);
v_fold_1577_ = lean_uint64_xor(v___y_1574_, v___x_1576_);
v___x_1578_ = 16ULL;
v___x_1579_ = lean_uint64_shift_right(v_fold_1577_, v___x_1578_);
v___x_1580_ = lean_uint64_xor(v_fold_1577_, v___x_1579_);
v___x_1581_ = lean_uint64_to_usize(v___x_1580_);
v___x_1582_ = lean_usize_of_nat(v___x_1572_);
v___x_1583_ = ((size_t)1ULL);
v___x_1584_ = lean_usize_sub(v___x_1582_, v___x_1583_);
v___x_1585_ = lean_usize_land(v___x_1581_, v___x_1584_);
v___x_1586_ = lean_array_uget_borrowed(v_buckets_1571_, v___x_1585_);
v___x_1587_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(v_a_1570_, v___x_1586_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_m_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(v_m_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_m_1590_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4(lean_object* v___x_1593_, lean_object* v_declName_1594_, lean_object* v_as_1595_, size_t v_sz_1596_, size_t v_i_1597_, lean_object* v_b_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_usize_dec_lt(v_i_1597_, v_sz_1596_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; 
lean_dec(v_declName_1594_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v_b_1598_);
return v___x_1603_;
}
else
{
lean_object* v___x_1604_; lean_object* v_modules_1605_; lean_object* v___x_1606_; lean_object* v_a_1607_; lean_object* v___x_1608_; lean_object* v_toImport_1609_; lean_object* v_module_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; 
v___x_1604_ = l_Lean_Environment_header(v___x_1593_);
v_modules_1605_ = lean_ctor_get(v___x_1604_, 3);
lean_inc_ref(v_modules_1605_);
lean_dec_ref(v___x_1604_);
v___x_1606_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1607_ = lean_array_uget_borrowed(v_as_1595_, v_i_1597_);
v___x_1608_ = lean_array_get(v___x_1606_, v_modules_1605_, v_a_1607_);
lean_dec_ref(v_modules_1605_);
v_toImport_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc_ref(v_toImport_1609_);
lean_dec(v___x_1608_);
v_module_1610_ = lean_ctor_get(v_toImport_1609_, 0);
lean_inc(v_module_1610_);
lean_dec_ref(v_toImport_1609_);
v___x_1611_ = lean_box(0);
v___x_1612_ = 0;
lean_inc(v_declName_1594_);
v___x_1613_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(v_module_1610_, v___x_1612_, v_declName_1594_, v___y_1599_, v___y_1600_);
if (lean_obj_tag(v___x_1613_) == 0)
{
size_t v___x_1614_; size_t v___x_1615_; 
lean_dec_ref_known(v___x_1613_, 1);
v___x_1614_ = ((size_t)1ULL);
v___x_1615_ = lean_usize_add(v_i_1597_, v___x_1614_);
v_i_1597_ = v___x_1615_;
v_b_1598_ = v___x_1611_;
goto _start;
}
else
{
lean_dec(v_declName_1594_);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4___boxed(lean_object* v___x_1617_, lean_object* v_declName_1618_, lean_object* v_as_1619_, lean_object* v_sz_1620_, lean_object* v_i_1621_, lean_object* v_b_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
size_t v_sz_boxed_1626_; size_t v_i_boxed_1627_; lean_object* v_res_1628_; 
v_sz_boxed_1626_ = lean_unbox_usize(v_sz_1620_);
lean_dec(v_sz_1620_);
v_i_boxed_1627_ = lean_unbox_usize(v_i_1621_);
lean_dec(v_i_1621_);
v_res_1628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4(v___x_1617_, v_declName_1618_, v_as_1619_, v_sz_boxed_1626_, v_i_boxed_1627_, v_b_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec_ref(v_as_1619_);
lean_dec_ref(v___x_1617_);
return v_res_1628_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2(lean_object* v_declName_1632_, uint8_t v_isMeta_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v_env_1642_; lean_object* v___y_1644_; lean_object* v___x_1657_; 
v___x_1637_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__0);
v___x_1638_ = lean_st_ref_get(v___y_1635_);
v_env_1642_ = lean_ctor_get(v___x_1638_, 0);
lean_inc_ref(v_env_1642_);
lean_dec(v___x_1638_);
v___x_1657_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1642_, v_declName_1632_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_dec_ref(v_env_1642_);
lean_dec(v_declName_1632_);
goto v___jp_1639_;
}
else
{
lean_object* v_val_1658_; lean_object* v___x_1659_; lean_object* v_modules_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_val_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_val_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = l_Lean_Environment_header(v_env_1642_);
v_modules_1660_ = lean_ctor_get(v___x_1659_, 3);
lean_inc_ref(v_modules_1660_);
lean_dec_ref(v___x_1659_);
v___x_1661_ = lean_array_get_size(v_modules_1660_);
v___x_1662_ = lean_nat_dec_lt(v_val_1658_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_dec_ref(v_modules_1660_);
lean_dec(v_val_1658_);
lean_dec_ref(v_env_1642_);
lean_dec(v_declName_1632_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___y_1666_; 
v___x_1663_ = lean_array_fget(v_modules_1660_, v_val_1658_);
lean_dec(v_val_1658_);
lean_dec_ref(v_modules_1660_);
v___x_1664_ = lean_st_ref_get(v___y_1635_);
if (v_isMeta_1633_ == 0)
{
lean_dec(v___x_1664_);
v___y_1666_ = v_isMeta_1633_;
goto v___jp_1665_;
}
else
{
lean_object* v_env_1677_; uint8_t v___x_1678_; 
v_env_1677_ = lean_ctor_get(v___x_1664_, 0);
lean_inc_ref(v_env_1677_);
lean_dec(v___x_1664_);
lean_inc(v_declName_1632_);
v___x_1678_ = l_Lean_isMarkedMeta(v_env_1677_, v_declName_1632_);
if (v___x_1678_ == 0)
{
v___y_1666_ = v_isMeta_1633_;
goto v___jp_1665_;
}
else
{
uint8_t v___x_1679_; 
v___x_1679_ = 0;
v___y_1666_ = v___x_1679_;
goto v___jp_1665_;
}
}
v___jp_1665_:
{
lean_object* v_toImport_1667_; lean_object* v_module_1668_; lean_object* v___x_1669_; 
v_toImport_1667_ = lean_ctor_get(v___x_1663_, 0);
lean_inc_ref(v_toImport_1667_);
lean_dec(v___x_1663_);
v_module_1668_ = lean_ctor_get(v_toImport_1667_, 0);
lean_inc(v_module_1668_);
lean_dec_ref(v_toImport_1667_);
lean_inc(v_declName_1632_);
v___x_1669_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3(v_module_1668_, v___y_1666_, v_declName_1632_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec_ref_known(v___x_1669_, 1);
v___x_1670_ = l_Lean_indirectModUseExt;
v___x_1671_ = lean_box(1);
v___x_1672_ = lean_box(0);
lean_inc_ref(v_env_1642_);
v___x_1673_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1637_, v___x_1670_, v_env_1642_, v___x_1671_, v___x_1672_);
v___x_1674_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(v___x_1673_, v_declName_1632_);
lean_dec(v___x_1673_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___closed__1));
v___y_1644_ = v___x_1675_;
goto v___jp_1643_;
}
else
{
lean_object* v_val_1676_; 
v_val_1676_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_val_1676_);
lean_dec_ref_known(v___x_1674_, 1);
v___y_1644_ = v_val_1676_;
goto v___jp_1643_;
}
}
else
{
lean_dec_ref(v_env_1642_);
lean_dec(v_declName_1632_);
return v___x_1669_;
}
}
}
}
v___jp_1639_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_box(0);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
v___jp_1643_:
{
lean_object* v___x_1645_; size_t v_sz_1646_; size_t v___x_1647_; lean_object* v___x_1648_; 
v___x_1645_ = lean_box(0);
v_sz_1646_ = lean_array_size(v___y_1644_);
v___x_1647_ = ((size_t)0ULL);
v___x_1648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__4(v_env_1642_, v_declName_1632_, v___y_1644_, v_sz_1646_, v___x_1647_, v___x_1645_, v___y_1634_, v___y_1635_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v_env_1642_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; 
v_unused_1656_ = lean_ctor_get(v___x_1648_, 0);
lean_dec(v_unused_1656_);
v___x_1650_ = v___x_1648_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_dec(v___x_1648_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1645_);
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1645_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
else
{
return v___x_1648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2___boxed(lean_object* v_declName_1680_, lean_object* v_isMeta_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_isMeta_boxed_1685_; lean_object* v_res_1686_; 
v_isMeta_boxed_1685_ = lean_unbox(v_isMeta_1681_);
v_res_1686_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2(v_declName_1680_, v_isMeta_boxed_1685_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(lean_object* v_as_x27_1687_, lean_object* v_b_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
if (lean_obj_tag(v_as_x27_1687_) == 0)
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_b_1688_);
return v___x_1692_;
}
else
{
lean_object* v_head_1693_; lean_object* v_tail_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; 
v_head_1693_ = lean_ctor_get(v_as_x27_1687_, 0);
v_tail_1694_ = lean_ctor_get(v_as_x27_1687_, 1);
v___x_1695_ = lean_box(0);
v___x_1696_ = 1;
lean_inc(v_head_1693_);
v___x_1697_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2(v_head_1693_, v___x_1696_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_dec_ref_known(v___x_1697_, 1);
v_as_x27_1687_ = v_tail_1694_;
v_b_1688_ = v___x_1695_;
goto _start;
}
else
{
return v___x_1697_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg___boxed(lean_object* v_as_x27_1699_, lean_object* v_b_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(v_as_x27_1699_, v_b_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v_as_x27_1699_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(lean_object* v_env_1705_, lean_object* v_declName_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v___x_1709_; lean_object* v_env_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; uint8_t v___x_1713_; 
v___x_1709_ = 0;
v_env_1710_ = l_Lean_Environment_setExporting(v_env_1705_, v___x_1709_);
lean_inc(v_declName_1706_);
v___x_1711_ = l_Lean_mkPrivateName(v_env_1710_, v_declName_1706_);
v___x_1712_ = 1;
lean_inc_ref(v_env_1710_);
v___x_1713_ = l_Lean_Environment_contains(v_env_1710_, v___x_1711_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; uint8_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1714_ = l_Lean_privateToUserName(v_declName_1706_);
v___x_1715_ = l_Lean_Environment_contains(v_env_1710_, v___x_1714_, v___x_1712_);
v___x_1716_ = lean_box(v___x_1715_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set(v___x_1717_, 1, v___y_1708_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec_ref(v_env_1710_);
lean_dec(v_declName_1706_);
v___x_1718_ = lean_box(v___x_1713_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
lean_ctor_set(v___x_1719_, 1, v___y_1708_);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0___boxed(lean_object* v_env_1720_, lean_object* v_declName_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0(v_env_1720_, v_declName_1721_, v___y_1722_, v___y_1723_);
lean_dec_ref(v___y_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(lean_object* v_x_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; lean_object* v_toCold_1731_; lean_object* v_env_1732_; lean_object* v_currRecDepth_1733_; lean_object* v_ref_1734_; lean_object* v_maxRecDepth_1735_; lean_object* v_currNamespace_1736_; lean_object* v_openDecls_1737_; lean_object* v_quotContext_1738_; lean_object* v_currMacroScope_1739_; lean_object* v___f_1740_; lean_object* v___f_1741_; lean_object* v___x_1742_; lean_object* v___f_1743_; lean_object* v___f_1744_; lean_object* v___f_1745_; lean_object* v_methods_1746_; lean_object* v___x_1747_; lean_object* v_nextMacroScope_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1730_ = lean_st_ref_get(v___y_1728_);
v_toCold_1731_ = lean_ctor_get(v___y_1727_, 0);
v_env_1732_ = lean_ctor_get(v___x_1730_, 0);
lean_inc_ref_n(v_env_1732_, 4);
lean_dec(v___x_1730_);
v_currRecDepth_1733_ = lean_ctor_get(v___y_1727_, 1);
v_ref_1734_ = lean_ctor_get(v___y_1727_, 2);
v_maxRecDepth_1735_ = lean_ctor_get(v_toCold_1731_, 3);
v_currNamespace_1736_ = lean_ctor_get(v_toCold_1731_, 4);
v_openDecls_1737_ = lean_ctor_get(v_toCold_1731_, 5);
v_quotContext_1738_ = lean_ctor_get(v_toCold_1731_, 8);
v_currMacroScope_1739_ = lean_ctor_get(v_toCold_1731_, 9);
v___f_1740_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1740_, 0, v_env_1732_);
v___f_1741_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1741_, 0, v_env_1732_);
v___x_1742_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1727_);
lean_inc_n(v_currNamespace_1736_, 3);
v___f_1743_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1743_, 0, v_currNamespace_1736_);
lean_inc_n(v_openDecls_1737_, 2);
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1744_, 0, v_env_1732_);
lean_closure_set(v___f_1744_, 1, v___x_1742_);
lean_closure_set(v___f_1744_, 2, v_currNamespace_1736_);
lean_closure_set(v___f_1744_, 3, v_openDecls_1737_);
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1745_, 0, v_env_1732_);
lean_closure_set(v___f_1745_, 1, v_currNamespace_1736_);
lean_closure_set(v___f_1745_, 2, v_openDecls_1737_);
v_methods_1746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1746_, 0, v___f_1741_);
lean_ctor_set(v_methods_1746_, 1, v___f_1743_);
lean_ctor_set(v_methods_1746_, 2, v___f_1740_);
lean_ctor_set(v_methods_1746_, 3, v___f_1745_);
lean_ctor_set(v_methods_1746_, 4, v___f_1744_);
v___x_1747_ = lean_st_ref_get(v___y_1728_);
v_nextMacroScope_1748_ = lean_ctor_get(v___x_1747_, 1);
lean_inc(v_nextMacroScope_1748_);
lean_dec(v___x_1747_);
lean_inc(v_ref_1734_);
lean_inc(v_maxRecDepth_1735_);
lean_inc(v_currRecDepth_1733_);
lean_inc(v_currMacroScope_1739_);
lean_inc(v_quotContext_1738_);
v___x_1749_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1749_, 0, v_methods_1746_);
lean_ctor_set(v___x_1749_, 1, v_quotContext_1738_);
lean_ctor_set(v___x_1749_, 2, v_currMacroScope_1739_);
lean_ctor_set(v___x_1749_, 3, v_currRecDepth_1733_);
lean_ctor_set(v___x_1749_, 4, v_maxRecDepth_1735_);
lean_ctor_set(v___x_1749_, 5, v_ref_1734_);
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1751_, 0, v_nextMacroScope_1748_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
lean_ctor_set(v___x_1751_, 2, v___x_1750_);
v___x_1752_ = lean_apply_2(v_x_1726_, v___x_1749_, v___x_1751_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v_a_1754_; lean_object* v_macroScope_1755_; lean_object* v_traceMsgs_1756_; lean_object* v_expandedMacroDecls_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 1);
lean_inc(v_a_1753_);
v_a_1754_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1752_, 2);
v_macroScope_1755_ = lean_ctor_get(v_a_1753_, 0);
lean_inc(v_macroScope_1755_);
v_traceMsgs_1756_ = lean_ctor_get(v_a_1753_, 1);
lean_inc(v_traceMsgs_1756_);
v_expandedMacroDecls_1757_ = lean_ctor_get(v_a_1753_, 2);
lean_inc(v_expandedMacroDecls_1757_);
lean_dec(v_a_1753_);
v___x_1758_ = lean_box(0);
v___x_1759_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(v_expandedMacroDecls_1757_, v___x_1758_, v___y_1727_, v___y_1728_);
lean_dec(v_expandedMacroDecls_1757_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v___x_1760_; lean_object* v_env_1761_; lean_object* v_ngen_1762_; lean_object* v_auxDeclNGen_1763_; lean_object* v_traceState_1764_; lean_object* v_cache_1765_; lean_object* v_recordedDeps_1766_; lean_object* v_messages_1767_; lean_object* v_infoState_1768_; lean_object* v_snapshotTasks_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref_known(v___x_1759_, 1);
v___x_1760_ = lean_st_ref_take(v___y_1728_);
v_env_1761_ = lean_ctor_get(v___x_1760_, 0);
v_ngen_1762_ = lean_ctor_get(v___x_1760_, 2);
v_auxDeclNGen_1763_ = lean_ctor_get(v___x_1760_, 3);
v_traceState_1764_ = lean_ctor_get(v___x_1760_, 4);
v_cache_1765_ = lean_ctor_get(v___x_1760_, 5);
v_recordedDeps_1766_ = lean_ctor_get(v___x_1760_, 6);
v_messages_1767_ = lean_ctor_get(v___x_1760_, 7);
v_infoState_1768_ = lean_ctor_get(v___x_1760_, 8);
v_snapshotTasks_1769_ = lean_ctor_get(v___x_1760_, 9);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v___x_1760_, 1);
lean_dec(v_unused_1796_);
v___x_1771_ = v___x_1760_;
v_isShared_1772_ = v_isSharedCheck_1795_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_snapshotTasks_1769_);
lean_inc(v_infoState_1768_);
lean_inc(v_messages_1767_);
lean_inc(v_recordedDeps_1766_);
lean_inc(v_cache_1765_);
lean_inc(v_traceState_1764_);
lean_inc(v_auxDeclNGen_1763_);
lean_inc(v_ngen_1762_);
lean_inc(v_env_1761_);
lean_dec(v___x_1760_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1795_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 1, v_macroScope_1755_);
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_env_1761_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_macroScope_1755_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_ngen_1762_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_auxDeclNGen_1763_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v_traceState_1764_);
lean_ctor_set(v_reuseFailAlloc_1794_, 5, v_cache_1765_);
lean_ctor_set(v_reuseFailAlloc_1794_, 6, v_recordedDeps_1766_);
lean_ctor_set(v_reuseFailAlloc_1794_, 7, v_messages_1767_);
lean_ctor_set(v_reuseFailAlloc_1794_, 8, v_infoState_1768_);
lean_ctor_set(v_reuseFailAlloc_1794_, 9, v_snapshotTasks_1769_);
v___x_1774_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = lean_st_ref_put(v___y_1728_, v___x_1774_);
v___x_1776_ = l_List_reverse___redArg(v_traceMsgs_1756_);
v___x_1777_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4(v___x_1776_, v___y_1727_, v___y_1728_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v___x_1777_, 0);
lean_dec(v_unused_1785_);
v___x_1779_ = v___x_1777_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_dec(v___x_1777_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v_a_1754_);
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1754_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v_a_1754_);
v_a_1786_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1777_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1777_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_traceMsgs_1756_);
lean_dec(v_macroScope_1755_);
lean_dec(v_a_1754_);
v_a_1797_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1759_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1759_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1805_; 
v_a_1805_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1752_, 2);
if (lean_obj_tag(v_a_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v_a_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v_a_1806_ = lean_ctor_get(v_a_1805_, 0);
lean_inc(v_a_1806_);
v_a_1807_ = lean_ctor_get(v_a_1805_, 1);
lean_inc_ref(v_a_1807_);
lean_dec_ref_known(v_a_1805_, 2);
v___x_1808_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___closed__0));
v___x_1809_ = lean_string_dec_eq(v_a_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1810_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_a_1807_);
v___x_1811_ = l_Lean_MessageData_ofFormat(v___x_1810_);
v___x_1812_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(v_a_1806_, v___x_1811_, v___y_1727_, v___y_1728_);
lean_dec(v_a_1806_);
return v___x_1812_;
}
else
{
lean_object* v___x_1813_; 
lean_dec_ref(v_a_1807_);
v___x_1813_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(v_a_1806_);
return v___x_1813_;
}
}
else
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg();
return v___x_1814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg___boxed(lean_object* v_x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(v_x_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1819_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__1));
v___x_1824_ = l_Lean_MessageData_ofFormat(v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(lean_object* v_stx_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v___y_1830_; lean_object* v_a_1831_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_env_1840_; lean_object* v___x_1841_; lean_object* v_toEnvExtension_1842_; lean_object* v_asyncMode_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1835_ = lean_box(1);
v___x_1836_ = lean_st_ref_get(v_a_1827_);
v_env_1840_ = lean_ctor_get(v___x_1836_, 0);
lean_inc_ref_n(v_env_1840_, 2);
lean_dec(v___x_1836_);
v___x_1841_ = l_Lean_Elab_deprecatedSyntaxReplacementExt;
v_toEnvExtension_1842_ = lean_ctor_get(v___x_1841_, 0);
v_asyncMode_1843_ = lean_ctor_get(v_toEnvExtension_1842_, 2);
v___x_1844_ = lean_box(0);
v___x_1845_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1835_, v___x_1841_, v_env_1840_, v_asyncMode_1843_, v___x_1844_);
lean_inc(v_stx_1825_);
v___x_1846_ = l_Lean_Syntax_getKind(v_stx_1825_);
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1845_, v___x_1846_);
lean_dec(v___x_1845_);
if (lean_obj_tag(v___x_1847_) == 1)
{
lean_object* v_val_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1951_; 
v_val_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1951_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_val_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1951_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1852_ = l_Lean_Parser_getSyntaxNodeKindCategories(v_env_1840_, v___x_1846_);
v___x_1853_ = lean_array_get_size(v___x_1852_);
v___x_1854_ = lean_unsigned_to_nat(1u);
v___x_1855_ = lean_nat_dec_eq(v___x_1853_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
lean_dec_ref(v___x_1852_);
lean_dec(v_val_1848_);
lean_dec(v_stx_1825_);
v___x_1856_ = l_Lean_MessageData_nil;
if (v_isShared_1851_ == 0)
{
lean_ctor_set_tag(v___x_1850_, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1856_);
v___x_1858_ = v___x_1850_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
else
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Syntax_getRange_x3f(v_stx_1825_, v___x_1855_);
if (lean_obj_tag(v___x_1860_) == 1)
{
lean_object* v_toCold_1861_; lean_object* v_val_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1946_; 
lean_del_object(v___x_1850_);
v_toCold_1861_ = lean_ctor_get(v_a_1826_, 0);
v_val_1862_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1864_ = v___x_1860_;
v_isShared_1865_ = v_isSharedCheck_1946_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_val_1862_);
lean_dec(v___x_1860_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1946_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_currRecDepth_1866_; lean_object* v_ref_1867_; uint16_t v_optionFlags_1868_; uint8_t v_suppressElabErrors_1869_; uint8_t v_isRecordingDeps_1870_; lean_object* v_fileMap_1871_; lean_object* v___x_1872_; 
v_currRecDepth_1866_ = lean_ctor_get(v_a_1826_, 1);
v_ref_1867_ = lean_ctor_get(v_a_1826_, 2);
v_optionFlags_1868_ = lean_ctor_get_uint16(v_a_1826_, sizeof(void*)*3);
v_suppressElabErrors_1869_ = lean_ctor_get_uint8(v_a_1826_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1870_ = lean_ctor_get_uint8(v_a_1826_, sizeof(void*)*3 + 3);
v_fileMap_1871_ = lean_ctor_get(v_toCold_1861_, 1);
v___x_1872_ = l_Lean_Syntax_getSubstring_x3f(v_stx_1825_, v___x_1855_, v___x_1855_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_del_object(v___x_1864_);
lean_dec(v_val_1862_);
lean_dec_ref(v___x_1852_);
lean_dec(v_val_1848_);
lean_dec(v_stx_1825_);
goto v___jp_1837_;
}
else
{
lean_object* v_val_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1945_; 
v_val_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1945_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_val_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1945_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_str_1877_; lean_object* v_source_1878_; uint8_t v___x_1879_; 
v_str_1877_ = lean_ctor_get(v_val_1873_, 0);
lean_inc_ref(v_str_1877_);
lean_dec(v_val_1873_);
v_source_1878_ = lean_ctor_get(v_fileMap_1871_, 0);
v___x_1879_ = lean_string_dec_eq(v_str_1877_, v_source_1878_);
lean_dec_ref(v_str_1877_);
if (v___x_1879_ == 0)
{
lean_del_object(v___x_1875_);
lean_del_object(v___x_1864_);
lean_dec(v_val_1862_);
lean_dec_ref(v___x_1852_);
lean_dec(v_val_1848_);
lean_dec(v_stx_1825_);
goto v___jp_1837_;
}
else
{
lean_object* v___x_1880_; lean_object* v___f_1881_; lean_object* v___x_1882_; 
v___x_1880_ = lean_box(v___x_1879_);
v___f_1881_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1881_, 0, v___x_1880_);
lean_inc(v_stx_1825_);
v___x_1882_ = l_Lean_Syntax_find_x3f(v_stx_1825_, v___f_1881_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; lean_object* v___x_1886_; 
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_array_fget(v___x_1852_, v___x_1883_);
lean_dec_ref(v___x_1852_);
v___x_1885_ = 0;
v___x_1886_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe(v_val_1848_, v_a_1826_, v_a_1827_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v_ref_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
lean_inc(v_stx_1825_);
v___x_1888_ = l_Lean_Syntax_unsetTrailing(v_stx_1825_);
v___x_1889_ = lean_apply_1(v_a_1887_, v___x_1888_);
v_ref_1890_ = l_Lean_replaceRef(v_stx_1825_, v_ref_1867_);
lean_inc(v_currRecDepth_1866_);
lean_inc_ref(v_toCold_1861_);
v___x_1891_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1891_, 0, v_toCold_1861_);
lean_ctor_set(v___x_1891_, 1, v_currRecDepth_1866_);
lean_ctor_set(v___x_1891_, 2, v_ref_1890_);
lean_ctor_set_uint16(v___x_1891_, sizeof(void*)*3, v_optionFlags_1868_);
lean_ctor_set_uint8(v___x_1891_, sizeof(void*)*3 + 2, v_suppressElabErrors_1869_);
lean_ctor_set_uint8(v___x_1891_, sizeof(void*)*3 + 3, v_isRecordingDeps_1870_);
v___x_1892_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(v___x_1889_, v___x_1891_, v_a_1827_);
lean_dec_ref_known(v___x_1891_, 3);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
v___x_1894_ = l_Lean_Syntax_eraseQuoteMacroScopes(v_a_1893_);
lean_inc(v_stx_1825_);
v___x_1895_ = l_Lean_Elab_DeprecatedSyntax_formatReplacement(v___x_1884_, v_stx_1825_, v___x_1894_, v_val_1862_, v_a_1826_, v_a_1827_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2, &l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2_once, _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___closed__2);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v_a_1896_);
v___x_1899_ = v___x_1864_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1896_);
v___x_1899_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
lean_ctor_set(v___x_1901_, 2, v___x_1900_);
lean_ctor_set(v___x_1901_, 3, v___x_1900_);
lean_ctor_set(v___x_1901_, 4, v___x_1900_);
lean_ctor_set(v___x_1901_, 5, v___x_1900_);
v___x_1902_ = 0;
v___x_1903_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1882_);
lean_ctor_set(v___x_1903_, 2, v___x_1882_);
lean_ctor_set_uint8(v___x_1903_, sizeof(void*)*3, v___x_1902_);
v___x_1904_ = lean_mk_empty_array_with_capacity(v___x_1854_);
v___x_1905_ = lean_array_push(v___x_1904_, v___x_1903_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v_stx_1825_);
v___x_1907_ = v___x_1875_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_stx_1825_);
v___x_1907_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_Lean_MessageData_hint(v___x_1897_, v___x_1905_, v___x_1907_, v___x_1900_, v___x_1885_, v_a_1826_, v_a_1827_);
lean_dec_ref(v___x_1905_);
if (lean_obj_tag(v___x_1908_) == 0)
{
return v___x_1908_;
}
else
{
lean_object* v_a_1909_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
v___y_1830_ = v___x_1908_;
v_a_1831_ = v_a_1909_;
goto v___jp_1829_;
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_del_object(v___x_1875_);
lean_del_object(v___x_1864_);
lean_dec(v_stx_1825_);
v_a_1912_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1895_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1895_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
lean_inc(v_a_1912_);
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
v___y_1830_ = v___x_1917_;
v_a_1831_ = v_a_1912_;
goto v___jp_1829_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v___x_1884_);
lean_del_object(v___x_1875_);
lean_del_object(v___x_1864_);
lean_dec(v_val_1862_);
lean_dec(v_stx_1825_);
v_a_1920_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1892_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1892_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
lean_inc(v_a_1920_);
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
v___y_1830_ = v___x_1925_;
v_a_1831_ = v_a_1920_;
goto v___jp_1829_;
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v___x_1884_);
lean_del_object(v___x_1875_);
lean_del_object(v___x_1864_);
lean_dec(v_val_1862_);
lean_dec(v_stx_1825_);
v_a_1928_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1886_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1886_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
lean_inc(v_a_1928_);
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
v___y_1830_ = v___x_1933_;
v_a_1831_ = v_a_1928_;
goto v___jp_1829_;
}
}
}
}
else
{
lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1943_; 
lean_del_object(v___x_1875_);
lean_del_object(v___x_1864_);
lean_dec(v_val_1862_);
lean_dec_ref(v___x_1852_);
lean_dec(v_val_1848_);
lean_dec(v_stx_1825_);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v___x_1882_, 0);
lean_dec(v_unused_1944_);
v___x_1937_ = v___x_1882_;
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
else
{
lean_dec(v___x_1882_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1943_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = l_Lean_MessageData_nil;
if (v_isShared_1938_ == 0)
{
lean_ctor_set_tag(v___x_1937_, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1939_);
v___x_1941_ = v___x_1937_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
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
lean_object* v___x_1947_; lean_object* v___x_1949_; 
lean_dec(v___x_1860_);
lean_dec_ref(v___x_1852_);
lean_dec(v_val_1848_);
lean_dec(v_stx_1825_);
v___x_1947_ = l_Lean_MessageData_nil;
if (v_isShared_1851_ == 0)
{
lean_ctor_set_tag(v___x_1850_, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1947_);
v___x_1949_ = v___x_1850_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_dec(v___x_1847_);
lean_dec(v___x_1846_);
lean_dec_ref(v_env_1840_);
lean_dec(v_stx_1825_);
v___x_1952_ = l_Lean_MessageData_nil;
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
v___jp_1829_:
{
uint8_t v___x_1832_; 
v___x_1832_ = l_Lean_Exception_isInterrupt(v_a_1831_);
lean_dec_ref(v_a_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec_ref(v___y_1830_);
v___x_1833_ = l_Lean_MessageData_nil;
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
else
{
return v___y_1830_;
}
}
v___jp_1837_:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = l_Lean_MessageData_nil;
v___x_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
return v___x_1839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint___boxed(lean_object* v_stx_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(v_stx_1954_, v_a_1955_, v_a_1956_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1(lean_object* v_00_u03b1_1959_, lean_object* v_x_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___redArg(v_x_1960_, v___y_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1964_, lean_object* v_x_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__1(v_00_u03b1_1964_, v_x_1965_, v___y_1966_, v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec_ref(v_x_1965_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6(lean_object* v_00_u03b1_1969_, lean_object* v_ref_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___redArg(v_ref_1970_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_ref_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__6(v_00_u03b1_1975_, v_ref_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7(lean_object* v_00_u03b1_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___redArg();
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7___boxed(lean_object* v_00_u03b1_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__7(v_00_u03b1_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0(lean_object* v_00_u03b1_1991_, lean_object* v_x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___redArg(v_x_1992_, v___y_1993_, v___y_1994_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0___boxed(lean_object* v_00_u03b1_1997_, lean_object* v_x_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0(v_00_u03b1_1997_, v_x_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3(lean_object* v_as_2003_, lean_object* v_as_x27_2004_, lean_object* v_b_2005_, lean_object* v_a_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___redArg(v_as_x27_2004_, v_b_2005_, v___y_2007_, v___y_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3___boxed(lean_object* v_as_2011_, lean_object* v_as_x27_2012_, lean_object* v_b_2013_, lean_object* v_a_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__3(v_as_2011_, v_as_x27_2012_, v_b_2013_, v_a_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v_as_x27_2012_);
lean_dec(v_as_2011_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5(lean_object* v_00_u03b1_2019_, lean_object* v_ref_2020_, lean_object* v_msg_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___redArg(v_ref_2020_, v_msg_2021_, v___y_2022_, v___y_2023_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2026_, lean_object* v_ref_2027_, lean_object* v_msg_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__5(v_00_u03b1_2026_, v_ref_2027_, v_msg_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v_ref_2027_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_2033_, lean_object* v_m_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___redArg(v_m_2034_, v_a_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2037_, lean_object* v_m_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5(v_00_u03b2_2037_, v_m_2038_, v_a_2039_);
lean_dec(v_a_2039_);
lean_dec_ref(v_m_2038_);
return v_res_2040_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_){
_start:
{
uint8_t v___x_2044_; 
v___x_2044_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___redArg(v_x_2042_, v_x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_2045_, lean_object* v_x_2046_, lean_object* v_x_2047_){
_start:
{
uint8_t v_res_2048_; lean_object* v_r_2049_; 
v_res_2048_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6(v_00_u03b2_2045_, v_x_2046_, v_x_2047_);
lean_dec_ref(v_x_2047_);
lean_dec_ref(v_x_2046_);
v_r_2049_ = lean_box(v_res_2048_);
return v_r_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_2050_, lean_object* v_a_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___redArg(v_a_2051_, v_x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_2054_, lean_object* v_a_2055_, lean_object* v_x_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__5_spec__9(v_00_u03b2_2054_, v_a_2055_, v_x_2056_);
lean_dec(v_x_2056_);
lean_dec(v_a_2055_);
return v_res_2057_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_2058_, lean_object* v_x_2059_, size_t v_x_2060_, lean_object* v_x_2061_){
_start:
{
uint8_t v___x_2062_; 
v___x_2062_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___redArg(v_x_2059_, v_x_2060_, v_x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
size_t v_x_11397__boxed_2067_; uint8_t v_res_2068_; lean_object* v_r_2069_; 
v_x_11397__boxed_2067_ = lean_unbox_usize(v_x_2065_);
lean_dec(v_x_2065_);
v_res_2068_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10(v_00_u03b2_2063_, v_x_2064_, v_x_11397__boxed_2067_, v_x_2066_);
lean_dec_ref(v_x_2066_);
lean_dec_ref(v_x_2064_);
v_r_2069_ = lean_box(v_res_2068_);
return v_r_2069_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13(lean_object* v_00_u03b2_2070_, lean_object* v_keys_2071_, lean_object* v_vals_2072_, lean_object* v_heq_2073_, lean_object* v_i_2074_, lean_object* v_k_2075_){
_start:
{
uint8_t v___x_2076_; 
v___x_2076_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___redArg(v_keys_2071_, v_i_2074_, v_k_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13___boxed(lean_object* v_00_u03b2_2077_, lean_object* v_keys_2078_, lean_object* v_vals_2079_, lean_object* v_heq_2080_, lean_object* v_i_2081_, lean_object* v_k_2082_){
_start:
{
uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_res_2083_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3_spec__6_spec__10_spec__13(v_00_u03b2_2077_, v_keys_2078_, v_vals_2079_, v_heq_2080_, v_i_2081_, v_k_2082_);
lean_dec_ref(v_k_2082_);
lean_dec_ref(v_vals_2079_);
lean_dec_ref(v_keys_2078_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__0));
v___x_2087_ = l_Lean_stringToMessageData(v___x_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix(lean_object* v_entry_2088_){
_start:
{
lean_object* v_text_x3f_2089_; 
v_text_x3f_2089_ = lean_ctor_get(v_entry_2088_, 1);
lean_inc(v_text_x3f_2089_);
lean_dec_ref(v_entry_2088_);
if (lean_obj_tag(v_text_x3f_2089_) == 0)
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9);
return v___x_2090_;
}
else
{
lean_object* v_val_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_val_2091_ = lean_ctor_get(v_text_x3f_2089_, 0);
lean_inc(v_val_2091_);
lean_dec_ref_known(v_text_x3f_2089_, 1);
v___x_2092_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1, &l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1_once, _init_l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix___closed__1);
v___x_2093_ = l_Lean_stringToMessageData(v_val_2091_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(lean_object* v_o_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v_env_2100_; lean_object* v___x_2101_; lean_object* v_toEnvExtension_2102_; lean_object* v_asyncMode_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v_merged_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2115_; 
v___x_2098_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_2099_ = lean_st_ref_get(v___y_2096_);
v_env_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_ref(v_env_2100_);
lean_dec(v___x_2099_);
v___x_2101_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_2102_ = lean_ctor_get(v___x_2101_, 0);
v_asyncMode_2103_ = lean_ctor_get(v_toEnvExtension_2102_, 2);
v___x_2104_ = lean_box(0);
v___x_2105_ = 0;
v___x_2106_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2098_, v___x_2101_, v_env_2100_, v_asyncMode_2103_, v___x_2104_, v___x_2105_);
v_merged_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v___x_2106_, 1);
lean_dec(v_unused_2116_);
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_merged_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v_merged_2107_);
lean_ctor_set(v___x_2109_, 0, v_o_2095_);
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_o_2095_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_merged_2107_);
v___x_2112_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg___boxed(lean_object* v_o_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(v_o_2117_, v___y_2118_);
lean_dec(v___y_2118_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2121_);
v___x_2125_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(v___x_2124_, v___y_2122_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0___boxed(lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2129_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4(lean_object* v_opts_2130_, lean_object* v_opt_2131_){
_start:
{
lean_object* v_name_2132_; lean_object* v_defValue_2133_; lean_object* v_map_2134_; lean_object* v___x_2135_; 
v_name_2132_ = lean_ctor_get(v_opt_2131_, 0);
v_defValue_2133_ = lean_ctor_get(v_opt_2131_, 1);
v_map_2134_ = lean_ctor_get(v_opts_2130_, 0);
v___x_2135_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2134_, v_name_2132_);
if (lean_obj_tag(v___x_2135_) == 0)
{
uint8_t v___x_2136_; 
v___x_2136_ = lean_unbox(v_defValue_2133_);
return v___x_2136_;
}
else
{
lean_object* v_val_2137_; 
v_val_2137_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_val_2137_);
lean_dec_ref_known(v___x_2135_, 1);
if (lean_obj_tag(v_val_2137_) == 1)
{
uint8_t v_v_2138_; 
v_v_2138_ = lean_ctor_get_uint8(v_val_2137_, 0);
lean_dec_ref_known(v_val_2137_, 0);
return v_v_2138_;
}
else
{
uint8_t v___x_2139_; 
lean_dec(v_val_2137_);
v___x_2139_ = lean_unbox(v_defValue_2133_);
return v___x_2139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_2140_, lean_object* v_opt_2141_){
_start:
{
uint8_t v_res_2142_; lean_object* v_r_2143_; 
v_res_2142_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4(v_opts_2140_, v_opt_2141_);
lean_dec_ref(v_opt_2141_);
lean_dec_ref(v_opts_2140_);
v_r_2143_ = lean_box(v_res_2142_);
return v_r_2143_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_2150_, lean_object* v_x_2151_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 1)
{
lean_object* v_pre_2152_; 
v_pre_2152_ = lean_ctor_get(v_x_2151_, 0);
switch(lean_obj_tag(v_pre_2152_))
{
case 1:
{
lean_object* v_pre_2153_; 
v_pre_2153_ = lean_ctor_get(v_pre_2152_, 0);
switch(lean_obj_tag(v_pre_2153_))
{
case 0:
{
lean_object* v_str_2154_; lean_object* v_str_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; 
v_str_2154_ = lean_ctor_get(v_x_2151_, 1);
v_str_2155_ = lean_ctor_get(v_pre_2152_, 1);
v___x_2156_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_Basic_2404873452____hygCtx___hyg_2_));
v___x_2157_ = lean_string_dec_eq(v_str_2155_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__0));
v___x_2159_ = lean_string_dec_eq(v_str_2155_, v___x_2158_);
if (v___x_2159_ == 0)
{
return v___x_2159_;
}
else
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__1));
v___x_2161_ = lean_string_dec_eq(v_str_2154_, v___x_2160_);
if (v___x_2161_ == 0)
{
return v___x_2161_;
}
else
{
return v_suppressElabErrors_2150_;
}
}
}
else
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__2));
v___x_2163_ = lean_string_dec_eq(v_str_2154_, v___x_2162_);
if (v___x_2163_ == 0)
{
return v___x_2163_;
}
else
{
return v_suppressElabErrors_2150_;
}
}
}
case 1:
{
lean_object* v_pre_2164_; 
v_pre_2164_ = lean_ctor_get(v_pre_2153_, 0);
if (lean_obj_tag(v_pre_2164_) == 0)
{
lean_object* v_str_2165_; lean_object* v_str_2166_; lean_object* v_str_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
v_str_2165_ = lean_ctor_get(v_x_2151_, 1);
v_str_2166_ = lean_ctor_get(v_pre_2152_, 1);
v_str_2167_ = lean_ctor_get(v_pre_2153_, 1);
v___x_2168_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__3));
v___x_2169_ = lean_string_dec_eq(v_str_2167_, v___x_2168_);
if (v___x_2169_ == 0)
{
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2170_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__4));
v___x_2171_ = lean_string_dec_eq(v_str_2166_, v___x_2170_);
if (v___x_2171_ == 0)
{
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___closed__5));
v___x_2173_ = lean_string_dec_eq(v_str_2165_, v___x_2172_);
if (v___x_2173_ == 0)
{
return v___x_2173_;
}
else
{
return v_suppressElabErrors_2150_;
}
}
}
}
else
{
uint8_t v___x_2174_; 
v___x_2174_ = 0;
return v___x_2174_;
}
}
default: 
{
uint8_t v___x_2175_; 
v___x_2175_ = 0;
return v___x_2175_;
}
}
}
case 0:
{
lean_object* v_str_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v_str_2176_ = lean_ctor_get(v_x_2151_, 1);
v___x_2177_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__4___closed__0));
v___x_2178_ = lean_string_dec_eq(v_str_2176_, v___x_2177_);
if (v___x_2178_ == 0)
{
return v___x_2178_;
}
else
{
return v_suppressElabErrors_2150_;
}
}
default: 
{
uint8_t v___x_2179_; 
v___x_2179_ = 0;
return v___x_2179_;
}
}
}
else
{
uint8_t v___x_2180_; 
v___x_2180_ = 0;
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_2181_, lean_object* v_x_2182_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2183_; uint8_t v_res_2184_; lean_object* v_r_2185_; 
v_suppressElabErrors_boxed_2183_ = lean_unbox(v_suppressElabErrors_2181_);
v_res_2184_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_2183_, v_x_2182_);
lean_dec(v_x_2182_);
v_r_2185_ = lean_box(v_res_2184_);
return v_r_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3(lean_object* v_ref_2186_, lean_object* v_msgData_2187_, uint8_t v_severity_2188_, uint8_t v_isSilent_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; uint8_t v___y_2198_; lean_object* v___y_2199_; uint8_t v___y_2200_; lean_object* v_toCold_2201_; lean_object* v___y_2202_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; uint8_t v___y_2234_; uint8_t v___y_2235_; uint8_t v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2258_; uint8_t v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; uint8_t v___y_2262_; uint8_t v___y_2263_; lean_object* v___y_2264_; uint8_t v___y_2268_; uint8_t v___y_2269_; uint8_t v___x_2279_; uint8_t v___y_2281_; uint8_t v___x_2287_; 
v___x_2279_ = 2;
v___x_2287_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2188_, v___x_2279_);
if (v___x_2287_ == 0)
{
v___y_2281_ = v___x_2287_;
goto v___jp_2280_;
}
else
{
uint8_t v___x_2288_; 
lean_inc_ref(v_msgData_2187_);
v___x_2288_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2187_);
if (v___x_2288_ == 0)
{
v___y_2281_ = v___x_2288_;
goto v___jp_2280_;
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec_ref(v_msgData_2187_);
v___x_2289_ = lean_box(0);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
}
v___jp_2193_:
{
lean_object* v_currNamespace_2203_; lean_object* v_openDecls_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v_env_2209_; lean_object* v_nextMacroScope_2210_; lean_object* v_ngen_2211_; lean_object* v_auxDeclNGen_2212_; lean_object* v_traceState_2213_; lean_object* v_cache_2214_; lean_object* v_recordedDeps_2215_; lean_object* v_messages_2216_; lean_object* v_infoState_2217_; lean_object* v_snapshotTasks_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2229_; 
v_currNamespace_2203_ = lean_ctor_get(v_toCold_2201_, 4);
v_openDecls_2204_ = lean_ctor_get(v_toCold_2201_, 5);
lean_inc(v_openDecls_2204_);
lean_inc(v_currNamespace_2203_);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_currNamespace_2203_);
lean_ctor_set(v___x_2205_, 1, v_openDecls_2204_);
v___x_2206_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v___y_2195_);
lean_inc_ref(v___y_2197_);
lean_inc_ref(v___y_2194_);
v___x_2207_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2207_, 0, v___y_2194_);
lean_ctor_set(v___x_2207_, 1, v___y_2199_);
lean_ctor_set(v___x_2207_, 2, v___y_2196_);
lean_ctor_set(v___x_2207_, 3, v___y_2197_);
lean_ctor_set(v___x_2207_, 4, v___x_2206_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*5, v___y_2200_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*5 + 1, v___y_2198_);
lean_ctor_set_uint8(v___x_2207_, sizeof(void*)*5 + 2, v_isSilent_2189_);
v___x_2208_ = lean_st_ref_take(v___y_2202_);
v_env_2209_ = lean_ctor_get(v___x_2208_, 0);
v_nextMacroScope_2210_ = lean_ctor_get(v___x_2208_, 1);
v_ngen_2211_ = lean_ctor_get(v___x_2208_, 2);
v_auxDeclNGen_2212_ = lean_ctor_get(v___x_2208_, 3);
v_traceState_2213_ = lean_ctor_get(v___x_2208_, 4);
v_cache_2214_ = lean_ctor_get(v___x_2208_, 5);
v_recordedDeps_2215_ = lean_ctor_get(v___x_2208_, 6);
v_messages_2216_ = lean_ctor_get(v___x_2208_, 7);
v_infoState_2217_ = lean_ctor_get(v___x_2208_, 8);
v_snapshotTasks_2218_ = lean_ctor_get(v___x_2208_, 9);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2220_ = v___x_2208_;
v_isShared_2221_ = v_isSharedCheck_2229_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_snapshotTasks_2218_);
lean_inc(v_infoState_2217_);
lean_inc(v_messages_2216_);
lean_inc(v_recordedDeps_2215_);
lean_inc(v_cache_2214_);
lean_inc(v_traceState_2213_);
lean_inc(v_auxDeclNGen_2212_);
lean_inc(v_ngen_2211_);
lean_inc(v_nextMacroScope_2210_);
lean_inc(v_env_2209_);
lean_dec(v___x_2208_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2229_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2222_ = lean_box(0);
v___x_2223_ = l_Lean_MessageLog_add(v___x_2207_, v_messages_2216_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 7, v___x_2223_);
v___x_2225_ = v___x_2220_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_env_2209_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_nextMacroScope_2210_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v_ngen_2211_);
lean_ctor_set(v_reuseFailAlloc_2228_, 3, v_auxDeclNGen_2212_);
lean_ctor_set(v_reuseFailAlloc_2228_, 4, v_traceState_2213_);
lean_ctor_set(v_reuseFailAlloc_2228_, 5, v_cache_2214_);
lean_ctor_set(v_reuseFailAlloc_2228_, 6, v_recordedDeps_2215_);
lean_ctor_set(v_reuseFailAlloc_2228_, 7, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2228_, 8, v_infoState_2217_);
lean_ctor_set(v_reuseFailAlloc_2228_, 9, v_snapshotTasks_2218_);
v___x_2225_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_st_ref_put(v___y_2202_, v___x_2225_);
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2222_);
return v___x_2227_;
}
}
}
v___jp_2230_:
{
lean_object* v_fileName_2239_; lean_object* v_fileMap_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2256_; 
v_fileName_2239_ = lean_ctor_get(v___y_2233_, 0);
v_fileMap_2240_ = lean_ctor_get(v___y_2233_, 1);
v___x_2241_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2187_);
v___x_2242_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_evalReplacementUnsafe_spec__0_spec__0_spec__1_spec__3(v___x_2241_, v___y_2190_, v___y_2191_);
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2256_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2256_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_inc_ref_n(v_fileMap_2240_, 2);
v___x_2247_ = l_Lean_FileMap_toPosition(v_fileMap_2240_, v___y_2237_);
lean_dec(v___y_2237_);
v___x_2248_ = l_Lean_FileMap_toPosition(v_fileMap_2240_, v___y_2238_);
lean_dec(v___y_2238_);
v___x_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
v___x_2250_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__0___closed__1));
if (v___y_2234_ == 0)
{
lean_del_object(v___x_2245_);
lean_dec_ref(v___y_2232_);
v___y_2194_ = v_fileName_2239_;
v___y_2195_ = v_a_2243_;
v___y_2196_ = v___x_2249_;
v___y_2197_ = v___x_2250_;
v___y_2198_ = v___y_2235_;
v___y_2199_ = v___x_2247_;
v___y_2200_ = v___y_2236_;
v_toCold_2201_ = v___y_2231_;
v___y_2202_ = v___y_2191_;
goto v___jp_2193_;
}
else
{
uint8_t v___x_2251_; 
lean_inc(v_a_2243_);
v___x_2251_ = l_Lean_MessageData_hasTag(v___y_2232_, v_a_2243_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2254_; 
lean_dec_ref_known(v___x_2249_, 1);
lean_dec_ref(v___x_2247_);
lean_dec(v_a_2243_);
v___x_2252_ = lean_box(0);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2252_);
v___x_2254_ = v___x_2245_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
else
{
lean_del_object(v___x_2245_);
v___y_2194_ = v_fileName_2239_;
v___y_2195_ = v_a_2243_;
v___y_2196_ = v___x_2249_;
v___y_2197_ = v___x_2250_;
v___y_2198_ = v___y_2235_;
v___y_2199_ = v___x_2247_;
v___y_2200_ = v___y_2236_;
v_toCold_2201_ = v___y_2231_;
v___y_2202_ = v___y_2191_;
goto v___jp_2193_;
}
}
}
}
v___jp_2257_:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Syntax_getTailPos_x3f(v___y_2261_, v___y_2263_);
lean_dec(v___y_2261_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_inc(v___y_2264_);
v___y_2231_ = v___y_2258_;
v___y_2232_ = v___y_2260_;
v___y_2233_ = v___y_2258_;
v___y_2234_ = v___y_2259_;
v___y_2235_ = v___y_2262_;
v___y_2236_ = v___y_2263_;
v___y_2237_ = v___y_2264_;
v___y_2238_ = v___y_2264_;
goto v___jp_2230_;
}
else
{
lean_object* v_val_2266_; 
v_val_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_val_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___y_2231_ = v___y_2258_;
v___y_2232_ = v___y_2260_;
v___y_2233_ = v___y_2258_;
v___y_2234_ = v___y_2259_;
v___y_2235_ = v___y_2262_;
v___y_2236_ = v___y_2263_;
v___y_2237_ = v___y_2264_;
v___y_2238_ = v_val_2266_;
goto v___jp_2230_;
}
}
v___jp_2267_:
{
lean_object* v_toCold_2270_; lean_object* v_ref_2271_; uint8_t v_suppressElabErrors_2272_; lean_object* v___x_2273_; lean_object* v___f_2274_; lean_object* v_ref_2275_; lean_object* v___x_2276_; 
v_toCold_2270_ = lean_ctor_get(v___y_2190_, 0);
v_ref_2271_ = lean_ctor_get(v___y_2190_, 2);
v_suppressElabErrors_2272_ = lean_ctor_get_uint8(v___y_2190_, sizeof(void*)*3 + 2);
v___x_2273_ = lean_box(v_suppressElabErrors_2272_);
v___f_2274_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2274_, 0, v___x_2273_);
v_ref_2275_ = l_Lean_replaceRef(v_ref_2186_, v_ref_2271_);
v___x_2276_ = l_Lean_Syntax_getPos_x3f(v_ref_2275_, v___y_2268_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v___x_2277_; 
v___x_2277_ = lean_unsigned_to_nat(0u);
v___y_2258_ = v_toCold_2270_;
v___y_2259_ = v_suppressElabErrors_2272_;
v___y_2260_ = v___f_2274_;
v___y_2261_ = v_ref_2275_;
v___y_2262_ = v___y_2269_;
v___y_2263_ = v___y_2268_;
v___y_2264_ = v___x_2277_;
goto v___jp_2257_;
}
else
{
lean_object* v_val_2278_; 
v_val_2278_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_val_2278_);
lean_dec_ref_known(v___x_2276_, 1);
v___y_2258_ = v_toCold_2270_;
v___y_2259_ = v_suppressElabErrors_2272_;
v___y_2260_ = v___f_2274_;
v___y_2261_ = v_ref_2275_;
v___y_2262_ = v___y_2269_;
v___y_2263_ = v___y_2268_;
v___y_2264_ = v_val_2278_;
goto v___jp_2257_;
}
}
v___jp_2280_:
{
uint8_t v___x_2282_; uint8_t v___x_2283_; 
v___x_2282_ = 1;
v___x_2283_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2188_, v___x_2282_);
if (v___x_2283_ == 0)
{
v___y_2268_ = v___y_2281_;
v___y_2269_ = v_severity_2188_;
goto v___jp_2267_;
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v___x_2284_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2190_);
v___x_2285_ = l_Lean_warningAsError;
v___x_2286_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3_spec__4(v___x_2284_, v___x_2285_);
lean_dec_ref(v___x_2284_);
if (v___x_2286_ == 0)
{
v___y_2268_ = v___y_2281_;
v___y_2269_ = v_severity_2188_;
goto v___jp_2267_;
}
else
{
v___y_2268_ = v___y_2281_;
v___y_2269_ = v___x_2279_;
goto v___jp_2267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3___boxed(lean_object* v_ref_2291_, lean_object* v_msgData_2292_, lean_object* v_severity_2293_, lean_object* v_isSilent_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
uint8_t v_severity_boxed_2298_; uint8_t v_isSilent_boxed_2299_; lean_object* v_res_2300_; 
v_severity_boxed_2298_ = lean_unbox(v_severity_2293_);
v_isSilent_boxed_2299_ = lean_unbox(v_isSilent_2294_);
v_res_2300_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3(v_ref_2291_, v_msgData_2292_, v_severity_boxed_2298_, v_isSilent_boxed_2299_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v_ref_2291_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2(lean_object* v_ref_2301_, lean_object* v_msgData_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v___x_2306_; uint8_t v___x_2307_; lean_object* v___x_2308_; 
v___x_2306_ = 1;
v___x_2307_ = 0;
v___x_2308_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2_spec__3(v_ref_2301_, v_msgData_2302_, v___x_2306_, v___x_2307_, v___y_2303_, v___y_2304_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2___boxed(lean_object* v_ref_2309_, lean_object* v_msgData_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2(v_ref_2309_, v_msgData_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v_ref_2309_);
return v_res_2314_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__0));
v___x_2317_ = l_Lean_stringToMessageData(v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__2));
v___x_2320_ = l_Lean_stringToMessageData(v___x_2319_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(lean_object* v_linterOption_2321_, lean_object* v_stx_2322_, lean_object* v_msg_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_name_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2345_; 
v_name_2327_ = lean_ctor_get(v_linterOption_2321_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_linterOption_2321_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; 
v_unused_2346_ = lean_ctor_get(v_linterOption_2321_, 1);
lean_dec(v_unused_2346_);
v___x_2329_ = v_linterOption_2321_;
v_isShared_2330_ = v_isSharedCheck_2345_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_name_2327_);
lean_dec(v_linterOption_2321_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2345_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2331_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1, &l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__1);
lean_inc(v_name_2327_);
v___x_2332_ = l_Lean_MessageData_ofName(v_name_2327_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set_tag(v___x_2329_, 7);
lean_ctor_set(v___x_2329_, 1, v___x_2332_);
lean_ctor_set(v___x_2329_, 0, v___x_2331_);
v___x_2334_ = v___x_2329_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v_disable_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2335_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3, &l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___closed__3);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v_disable_2337_ = l_Lean_MessageData_note(v___x_2336_);
v___x_2338_ = l_Lean_Linter_linterMessageTag;
v___x_2339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2339_, 0, v_msg_2323_);
lean_ctor_set(v___x_2339_, 1, v_disable_2337_);
v___x_2340_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2341_, 0, v_name_2327_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
lean_inc(v_stx_2322_);
v___x_2342_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2342_, 0, v_stx_2322_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1_spec__2(v_stx_2322_, v___x_2342_, v___y_2324_, v___y_2325_);
lean_dec(v_stx_2322_);
return v___x_2343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1___boxed(lean_object* v_linterOption_2347_, lean_object* v_stx_2348_, lean_object* v_msg_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v_linterOption_2347_, v_stx_2348_, v_msg_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2353_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__1(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__0));
v___x_2356_ = l_Lean_stringToMessageData(v___x_2355_);
return v___x_2356_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__3(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__2));
v___x_2359_ = l_Lean_stringToMessageData(v___x_2358_);
return v___x_2359_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__5(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__4));
v___x_2362_ = l_Lean_stringToMessageData(v___x_2361_);
return v___x_2362_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__7(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__6));
v___x_2365_ = l_Lean_stringToMessageData(v___x_2364_);
return v___x_2365_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__8));
v___x_2368_ = l_Lean_stringToMessageData(v___x_2367_);
return v___x_2368_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__11(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__10));
v___x_2371_ = l_Lean_stringToMessageData(v___x_2370_);
return v___x_2371_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__13(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__12));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___closed__15(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___closed__14));
v___x_2377_ = l_Lean_stringToMessageData(v___x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax(lean_object* v_stx_2378_, lean_object* v_macroStack_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_env_2385_; lean_object* v___x_2386_; lean_object* v_toEnvExtension_2387_; lean_object* v_asyncMode_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2383_ = lean_box(1);
v___x_2384_ = lean_st_ref_get(v_a_2381_);
v_env_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc_ref(v_env_2385_);
lean_dec(v___x_2384_);
v___x_2386_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_2387_ = lean_ctor_get(v___x_2386_, 0);
v_asyncMode_2388_ = lean_ctor_get(v_toEnvExtension_2387_, 2);
lean_inc(v_stx_2378_);
v___x_2389_ = l_Lean_Syntax_getKind(v_stx_2378_);
v___x_2390_ = lean_box(0);
v___x_2391_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2383_, v___x_2386_, v_env_2385_, v_asyncMode_2388_, v___x_2390_);
v___x_2392_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2391_, v___x_2389_);
lean_dec(v___x_2391_);
if (lean_obj_tag(v___x_2392_) == 1)
{
lean_object* v_val_2393_; lean_object* v___x_2394_; lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2519_; 
v_val_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_val_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2394_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(v_a_2380_, v_a_2381_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2519_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2519_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_2400_ = l_Lean_Linter_getLinterValue(v___x_2399_, v_a_2395_);
lean_dec(v_a_2395_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
lean_dec(v_val_2393_);
lean_dec(v___x_2389_);
lean_dec(v_macroStack_2379_);
lean_dec(v_stx_2378_);
v___x_2401_ = lean_box(0);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2401_);
v___x_2403_ = v___x_2397_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
else
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_del_object(v___x_2397_);
v___x_2405_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix(v_val_2393_);
v___x_2406_ = l_Lean_Syntax_getHeadInfo(v_stx_2378_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v___x_2407_; 
lean_dec_ref_known(v___x_2406_, 4);
lean_dec(v_macroStack_2379_);
lean_inc(v_stx_2378_);
v___x_2407_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(v_stx_2378_, v_a_2380_, v_a_2381_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__1);
v___x_2410_ = l_Lean_MessageData_ofName(v___x_2389_);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__3);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
lean_ctor_set(v___x_2414_, 1, v___x_2405_);
v___x_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v_a_2408_);
v___x_2416_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2399_, v_stx_2378_, v___x_2415_, v_a_2380_, v_a_2381_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; 
v_unused_2425_ = lean_ctor_get(v___x_2416_, 0);
lean_dec(v_unused_2425_);
v___x_2418_ = v___x_2416_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_dec(v___x_2416_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = lean_box(0);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
return v___x_2416_;
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec_ref(v___x_2405_);
lean_dec(v___x_2389_);
lean_dec(v_stx_2378_);
v_a_2426_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2407_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2407_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_dec(v___x_2406_);
if (lean_obj_tag(v_macroStack_2379_) == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2434_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__1);
v___x_2435_ = l_Lean_MessageData_ofName(v___x_2389_);
v___x_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__3);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v___x_2405_);
v___x_2440_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2399_, v_stx_2378_, v___x_2439_, v_a_2380_, v_a_2381_);
return v___x_2440_;
}
else
{
lean_object* v_head_2441_; lean_object* v_tail_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v_stx_2378_);
v_head_2441_ = lean_ctor_get(v_macroStack_2379_, 0);
v_tail_2442_ = lean_ctor_get(v_macroStack_2379_, 1);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_macroStack_2379_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2444_ = v_macroStack_2379_;
v_isShared_2445_ = v_isSharedCheck_2518_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_tail_2442_);
lean_inc(v_head_2441_);
lean_dec(v_macroStack_2379_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2518_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
if (lean_obj_tag(v_tail_2442_) == 0)
{
lean_object* v_before_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2466_; 
v_before_2446_ = lean_ctor_get(v_head_2441_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_head_2441_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; 
v_unused_2467_ = lean_ctor_get(v_head_2441_, 1);
lean_dec(v_unused_2467_);
v___x_2448_ = v_head_2441_;
v_isShared_2449_ = v_isSharedCheck_2466_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_before_2446_);
lean_dec(v_head_2441_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2466_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2450_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__5, &l_Lean_Elab_checkDeprecatedSyntax___closed__5_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__5);
lean_inc(v_before_2446_);
v___x_2451_ = l_Lean_Syntax_getKind(v_before_2446_);
v___x_2452_ = l_Lean_MessageData_ofName(v___x_2451_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set_tag(v___x_2448_, 7);
lean_ctor_set(v___x_2448_, 1, v___x_2452_);
lean_ctor_set(v___x_2448_, 0, v___x_2450_);
v___x_2454_ = v___x_2448_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__7, &l_Lean_Elab_checkDeprecatedSyntax___closed__7_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__7);
if (v_isShared_2445_ == 0)
{
lean_ctor_set_tag(v___x_2444_, 7);
lean_ctor_set(v___x_2444_, 1, v___x_2455_);
lean_ctor_set(v___x_2444_, 0, v___x_2454_);
v___x_2457_ = v___x_2444_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2458_ = l_Lean_MessageData_ofName(v___x_2389_);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v___x_2405_);
v___x_2463_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2399_, v_before_2446_, v___x_2462_, v_a_2380_, v_a_2381_);
return v___x_2463_;
}
}
}
}
else
{
lean_object* v_head_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2516_; 
v_head_2468_ = lean_ctor_get(v_tail_2442_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_tail_2442_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v_tail_2442_, 1);
lean_dec(v_unused_2517_);
v___x_2470_ = v_tail_2442_;
v_isShared_2471_ = v_isSharedCheck_2516_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_head_2468_);
lean_dec(v_tail_2442_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2516_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_before_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2514_; 
v_before_2472_ = lean_ctor_get(v_head_2441_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_head_2441_);
if (v_isSharedCheck_2514_ == 0)
{
lean_object* v_unused_2515_; 
v_unused_2515_ = lean_ctor_get(v_head_2441_, 1);
lean_dec(v_unused_2515_);
v___x_2474_ = v_head_2441_;
v_isShared_2475_ = v_isSharedCheck_2514_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_before_2472_);
lean_dec(v_head_2441_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2514_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_before_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2512_; 
v_before_2476_ = lean_ctor_get(v_head_2468_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_head_2468_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v_head_2468_, 1);
lean_dec(v_unused_2513_);
v___x_2478_ = v_head_2468_;
v_isShared_2479_ = v_isSharedCheck_2512_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_before_2476_);
lean_dec(v_head_2468_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2512_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___y_2483_; uint8_t v___x_2505_; 
v___x_2480_ = l_Lean_Syntax_getKind(v_before_2476_);
lean_inc(v_before_2472_);
v___x_2481_ = l_Lean_Syntax_getKind(v_before_2472_);
v___x_2505_ = lean_name_eq(v___x_2480_, v___x_2481_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2506_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__13, &l_Lean_Elab_checkDeprecatedSyntax___closed__13_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__13);
v___x_2507_ = l_Lean_MessageData_ofName(v___x_2480_);
v___x_2508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2506_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__15, &l_Lean_Elab_checkDeprecatedSyntax___closed__15_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__15);
v___x_2510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
v___y_2483_ = v___x_2510_;
goto v___jp_2482_;
}
else
{
lean_object* v___x_2511_; 
lean_dec(v___x_2480_);
v___x_2511_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint_spec__0_spec__2_spec__3___closed__9);
v___y_2483_ = v___x_2511_;
goto v___jp_2482_;
}
v___jp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2487_; 
v___x_2484_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__5, &l_Lean_Elab_checkDeprecatedSyntax___closed__5_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__5);
v___x_2485_ = l_Lean_MessageData_ofName(v___x_2481_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set_tag(v___x_2478_, 7);
lean_ctor_set(v___x_2478_, 1, v___x_2485_);
lean_ctor_set(v___x_2478_, 0, v___x_2484_);
v___x_2487_ = v___x_2478_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2484_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2488_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9);
if (v_isShared_2471_ == 0)
{
lean_ctor_set_tag(v___x_2470_, 7);
lean_ctor_set(v___x_2470_, 1, v___x_2488_);
lean_ctor_set(v___x_2470_, 0, v___x_2487_);
v___x_2490_ = v___x_2470_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2488_);
v___x_2490_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2492_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set_tag(v___x_2474_, 7);
lean_ctor_set(v___x_2474_, 1, v___y_2483_);
lean_ctor_set(v___x_2474_, 0, v___x_2490_);
v___x_2492_ = v___x_2474_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___y_2483_);
v___x_2492_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2493_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__11, &l_Lean_Elab_checkDeprecatedSyntax___closed__11_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__11);
if (v_isShared_2445_ == 0)
{
lean_ctor_set_tag(v___x_2444_, 7);
lean_ctor_set(v___x_2444_, 1, v___x_2493_);
lean_ctor_set(v___x_2444_, 0, v___x_2492_);
v___x_2495_ = v___x_2444_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2496_ = l_Lean_MessageData_ofName(v___x_2389_);
v___x_2497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2495_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
lean_ctor_set(v___x_2498_, 1, v___x_2488_);
v___x_2499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___x_2405_);
v___x_2500_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2399_, v_before_2472_, v___x_2499_, v_a_2380_, v_a_2381_);
return v___x_2500_;
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
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec(v___x_2392_);
lean_dec(v___x_2389_);
lean_dec(v_macroStack_2379_);
lean_dec(v_stx_2378_);
v___x_2520_ = lean_box(0);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___boxed(lean_object* v_stx_2522_, lean_object* v_macroStack_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Elab_checkDeprecatedSyntax(v_stx_2522_, v_macroStack_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0(lean_object* v_o_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___redArg(v_o_2528_, v___y_2530_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0___boxed(lean_object* v_o_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0_spec__0(v_o_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2537_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__0));
v___x_2540_ = l_Lean_stringToMessageData(v___x_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax(lean_object* v_stx_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v_env_2547_; lean_object* v___x_2548_; lean_object* v_toEnvExtension_2549_; lean_object* v_asyncMode_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2545_ = lean_box(1);
v___x_2546_ = lean_st_ref_get(v_a_2543_);
v_env_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc_ref(v_env_2547_);
lean_dec(v___x_2546_);
v___x_2548_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_2549_ = lean_ctor_get(v___x_2548_, 0);
v_asyncMode_2550_ = lean_ctor_get(v_toEnvExtension_2549_, 2);
v___x_2551_ = lean_box(0);
v___x_2552_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2545_, v___x_2548_, v_env_2547_, v_asyncMode_2550_, v___x_2551_);
lean_inc(v_stx_2541_);
v___x_2553_ = l_Lean_Syntax_getKind(v_stx_2541_);
v___x_2554_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_2552_, v___x_2553_);
lean_dec(v___x_2552_);
if (lean_obj_tag(v___x_2554_) == 1)
{
lean_object* v_val_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2595_; 
v_val_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2595_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_val_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2595_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_Syntax_getHeadInfo(v_stx_2541_);
if (lean_obj_tag(v___x_2559_) == 1)
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
lean_dec_ref_known(v___x_2559_, 2);
lean_dec(v_val_2555_);
lean_dec(v___x_2553_);
lean_dec(v_stx_2541_);
v___x_2560_ = lean_box(0);
if (v_isShared_2558_ == 0)
{
lean_ctor_set_tag(v___x_2557_, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2560_);
v___x_2562_ = v___x_2557_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
else
{
lean_object* v___x_2564_; lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2594_; 
lean_dec(v___x_2559_);
lean_del_object(v___x_2557_);
v___x_2564_ = l_Lean_Linter_getLinterOptions___at___00Lean_Elab_checkDeprecatedSyntax_spec__0(v_a_2542_, v_a_2543_);
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2594_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2594_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2569_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_2570_ = l_Lean_Linter_getLinterValue(v___x_2569_, v_a_2565_);
lean_dec(v_a_2565_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
lean_dec(v_val_2555_);
lean_dec(v___x_2553_);
lean_dec(v_stx_2541_);
v___x_2571_ = lean_box(0);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2571_);
v___x_2573_ = v___x_2567_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
else
{
lean_object* v___x_2575_; 
lean_del_object(v___x_2567_);
lean_inc(v_stx_2541_);
v___x_2575_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_mkReplacementHint(v_stx_2541_, v_a_2542_, v_a_2543_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1, &l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1_once, _init_l_Lean_Elab_checkDeprecatedQuotedSyntax___closed__1);
v___x_2578_ = l_Lean_MessageData_ofName(v___x_2553_);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___closed__9);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l___private_Lean_Elab_DeprecatedSyntax_Basic_0__Lean_Elab_SyntaxDeprecationEntry_textSuffix(v_val_2555_);
v___x_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v_a_2576_);
v___x_2585_ = l_Lean_Linter_logLint___at___00Lean_Elab_checkDeprecatedSyntax_spec__1(v___x_2569_, v_stx_2541_, v___x_2584_, v_a_2542_, v_a_2543_);
return v___x_2585_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_val_2555_);
lean_dec(v___x_2553_);
lean_dec(v_stx_2541_);
v_a_2586_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2575_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2575_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
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
lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_dec(v___x_2554_);
lean_dec(v___x_2553_);
lean_dec(v_stx_2541_);
v___x_2596_ = lean_box(0);
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedQuotedSyntax___boxed(lean_object* v_stx_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Elab_checkDeprecatedQuotedSyntax(v_stx_2598_, v_a_2599_, v_a_2600_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
return v_res_2602_;
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
