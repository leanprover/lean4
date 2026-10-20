// Lean compiler output
// Module: Lean.Linter.DefProp
// Imports: public import Lean.Linter.Basic public import Lean.Linter.Util
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Linter_getDeclsByBody(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isDefinition(lean_object*);
lean_object* l_Lean_ConstantInfo_hints(lean_object*);
uint8_t l_Lean_ReducibilityHints_isAbbrev(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "defProp"};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 155, 102, 62, 63, 148, 150, 28)}};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 175, .m_capacity = 175, .m_length = 174, .m_data = "enable the `defProp` linter, which warns when a `def` is used to introduce a declaration whose type is a `Prop`; such a declaration should be written using `theorem` instead."};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(11, 14, 230, 184, 252, 64, 196, 245)}};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_defProp;
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Definition `"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` is a proposition; use `theorem` instead of `def`"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DefProp_defPropLinter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_DefProp_defPropLinter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_DefProp_defPropLinter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_DefProp_defPropLinter___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_DefProp_defPropLinter___closed__0 = (const lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__0_value;
static const lean_closure_object l_Lean_Linter_DefProp_defPropLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__0_value)} };
static const lean_object* l_Lean_Linter_DefProp_defPropLinter___closed__1 = (const lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__1_value;
static const lean_string_object l_Lean_Linter_DefProp_defPropLinter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "DefProp"};
static const lean_object* l_Lean_Linter_DefProp_defPropLinter___closed__2 = (const lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__2_value;
static const lean_string_object l_Lean_Linter_DefProp_defPropLinter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "defPropLinter"};
static const lean_object* l_Lean_Linter_DefProp_defPropLinter___closed__3 = (const lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__3_value;
static const lean_ctor_object l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_1),((lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(101, 170, 97, 95, 31, 222, 192, 208)}};
static const lean_ctor_object l_Lean_Linter_DefProp_defPropLinter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_2),((lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__3_value),LEAN_SCALAR_PTR_LITERAL(157, 41, 87, 225, 127, 238, 120, 159)}};
static const lean_object* l_Lean_Linter_DefProp_defPropLinter___closed__4 = (const lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__4_value;
static const lean_ctor_object l_Lean_Linter_DefProp_defPropLinter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__1_value),((lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__4_value)}};
static const lean_object* l_Lean_Linter_DefProp_defPropLinter___closed__5 = (const lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_DefProp_defPropLinter = (const lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; lean_object* v_infoState_62_; lean_object* v_trees_63_; lean_object* v___x_64_; 
v___x_61_ = lean_st_ref_get(v___y_59_);
v_infoState_62_ = lean_ctor_get(v___x_61_, 8);
lean_inc_ref(v_infoState_62_);
lean_dec(v___x_61_);
v_trees_63_ = lean_ctor_get(v_infoState_62_, 2);
lean_inc_ref(v_trees_63_);
lean_dec_ref(v_infoState_62_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v_trees_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg___boxed(lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(v___y_65_);
lean_dec(v___y_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1(lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___boxed(lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1(v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(lean_object* v_o_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_env_81_; lean_object* v___x_82_; lean_object* v_toEnvExtension_83_; lean_object* v_asyncMode_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v_merged_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v___x_79_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_80_ = lean_st_ref_get(v___y_77_);
v_env_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc_ref(v_env_81_);
lean_dec(v___x_80_);
v___x_82_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_83_ = lean_ctor_get(v___x_82_, 0);
v_asyncMode_84_ = lean_ctor_get(v_toEnvExtension_83_, 2);
v___x_85_ = lean_box(0);
v___x_86_ = 0;
v___x_87_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_79_, v___x_82_, v_env_81_, v_asyncMode_84_, v___x_85_, v___x_86_);
v_merged_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v___x_87_, 1);
lean_dec(v_unused_97_);
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_merged_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_merged_88_);
lean_ctor_set(v___x_90_, 0, v_o_76_);
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_o_76_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_merged_88_);
v___x_93_ = v_reuseFailAlloc_95_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_o_98_, v___y_99_);
lean_dec(v___y_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_scopes_107_; lean_object* v___x_108_; lean_object* v_opts_109_; lean_object* v___x_110_; 
v___x_105_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_106_ = lean_st_ref_get(v___y_103_);
v_scopes_107_ = lean_ctor_get(v___x_106_, 2);
lean_inc(v_scopes_107_);
lean_dec(v___x_106_);
v___x_108_ = l_List_head_x21___redArg(v___x_105_, v_scopes_107_);
lean_dec(v_scopes_107_);
v_opts_109_ = lean_ctor_get(v___x_108_, 1);
lean_inc_ref(v_opts_109_);
lean_dec(v___x_108_);
v___x_110_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_opts_109_, v___y_103_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0___boxed(lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_114_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_115_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_119_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
lean_ctor_set(v___x_121_, 2, v___x_120_);
lean_ctor_set(v___x_121_, 3, v___x_120_);
lean_ctor_set(v___x_121_, 4, v___x_119_);
lean_ctor_set(v___x_121_, 5, v___x_119_);
lean_ctor_set(v___x_121_, 6, v___x_119_);
lean_ctor_set(v___x_121_, 7, v___x_119_);
lean_ctor_set(v___x_121_, 8, v___x_119_);
lean_ctor_set(v___x_121_, 9, v___x_119_);
lean_ctor_set(v___x_121_, 10, v___x_119_);
lean_ctor_set(v___x_121_, 11, v___x_118_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_unsigned_to_nat(32u);
v___x_123_ = lean_mk_empty_array_with_capacity(v___x_122_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_125_ = ((size_t)5ULL);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_unsigned_to_nat(32u);
v___x_128_ = lean_mk_empty_array_with_capacity(v___x_127_);
v___x_129_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3);
v___x_130_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_126_);
lean_ctor_set(v___x_130_, 3, v___x_126_);
lean_ctor_set_usize(v___x_130_, 4, v___x_125_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_131_ = lean_box(1);
v___x_132_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4);
v___x_133_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1);
v___x_134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
lean_ctor_set(v___x_134_, 2, v___x_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_msgData_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_138_; lean_object* v_env_139_; uint8_t v___x_140_; lean_object* v_env_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v_scopes_144_; lean_object* v___x_145_; lean_object* v_opts_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_138_ = lean_st_ref_get(v___y_136_);
v_env_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_env_139_);
lean_dec(v___x_138_);
v___x_140_ = 0;
v_env_141_ = l_Lean_Environment_setRecordingDeps(v_env_139_, v___x_140_);
v___x_142_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_143_ = lean_st_ref_get(v___y_136_);
v_scopes_144_ = lean_ctor_get(v___x_143_, 2);
lean_inc(v_scopes_144_);
lean_dec(v___x_143_);
v___x_145_ = l_List_head_x21___redArg(v___x_142_, v_scopes_144_);
lean_dec(v_scopes_144_);
v_opts_146_ = lean_ctor_get(v___x_145_, 1);
lean_inc_ref(v_opts_146_);
lean_dec(v___x_145_);
v___x_147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2);
v___x_148_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5);
v___x_149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_149_, 0, v_env_141_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
lean_ctor_set(v___x_149_, 2, v___x_148_);
lean_ctor_set(v___x_149_, 3, v_opts_146_);
v___x_150_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_msgData_135_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_msgData_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_msgData_152_, v___y_153_);
lean_dec(v___y_153_);
return v_res_155_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(uint8_t v_suppressElabErrors_157_, lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_158_) == 1)
{
lean_object* v_pre_159_; 
v_pre_159_ = lean_ctor_get(v_x_158_, 0);
if (lean_obj_tag(v_pre_159_) == 0)
{
lean_object* v_str_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_str_160_ = lean_ctor_get(v_x_158_, 1);
v___x_161_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0));
v___x_162_ = lean_string_dec_eq(v_str_160_, v___x_161_);
if (v___x_162_ == 0)
{
return v___x_162_;
}
else
{
return v_suppressElabErrors_157_;
}
}
else
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
}
else
{
uint8_t v___x_164_; 
v___x_164_ = 0;
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_165_, lean_object* v_x_166_){
_start:
{
uint8_t v_suppressElabErrors_boxed_167_; uint8_t v_res_168_; lean_object* v_r_169_; 
v_suppressElabErrors_boxed_167_ = lean_unbox(v_suppressElabErrors_165_);
v_res_168_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(v_suppressElabErrors_boxed_167_, v_x_166_);
lean_dec(v_x_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(lean_object* v_opts_170_, lean_object* v_opt_171_){
_start:
{
lean_object* v_name_172_; lean_object* v_defValue_173_; lean_object* v_map_174_; lean_object* v___x_175_; 
v_name_172_ = lean_ctor_get(v_opt_171_, 0);
v_defValue_173_ = lean_ctor_get(v_opt_171_, 1);
v_map_174_ = lean_ctor_get(v_opts_170_, 0);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_174_, v_name_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
uint8_t v___x_176_; 
v___x_176_ = lean_unbox(v_defValue_173_);
return v___x_176_;
}
else
{
lean_object* v_val_177_; 
v_val_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_175_, 1);
if (lean_obj_tag(v_val_177_) == 1)
{
uint8_t v_v_178_; 
v_v_178_ = lean_ctor_get_uint8(v_val_177_, 0);
lean_dec_ref_known(v_val_177_, 0);
return v_v_178_;
}
else
{
uint8_t v___x_179_; 
lean_dec(v_val_177_);
v___x_179_ = lean_unbox(v_defValue_173_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_opts_180_, lean_object* v_opt_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(v_opts_180_, v_opt_181_);
lean_dec_ref(v_opt_181_);
lean_dec_ref(v_opts_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(lean_object* v_ref_185_, lean_object* v_msgData_186_, uint8_t v_severity_187_, uint8_t v_isSilent_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___y_193_; uint8_t v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; uint8_t v___y_198_; lean_object* v___y_199_; lean_object* v___y_200_; uint8_t v___y_258_; lean_object* v___y_259_; uint8_t v___y_260_; lean_object* v___y_261_; uint8_t v___y_284_; lean_object* v___y_285_; uint8_t v___y_286_; lean_object* v___y_287_; uint8_t v___y_291_; uint8_t v___y_292_; uint8_t v___x_307_; uint8_t v___y_309_; uint8_t v___x_319_; 
v___x_307_ = 2;
v___x_319_ = l_Lean_instBEqMessageSeverity_beq(v_severity_187_, v___x_307_);
if (v___x_319_ == 0)
{
v___y_309_ = v___x_319_;
goto v___jp_308_;
}
else
{
uint8_t v___x_320_; 
lean_inc_ref(v_msgData_186_);
v___x_320_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_186_);
if (v___x_320_ == 0)
{
v___y_309_ = v___x_320_;
goto v___jp_308_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v_msgData_186_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
v___jp_192_:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Elab_Command_getScope___redArg(v___y_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v_currNamespace_203_; lean_object* v___x_204_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_201_, 1);
v_currNamespace_203_ = lean_ctor_get(v_a_202_, 2);
lean_inc(v_currNamespace_203_);
lean_dec(v_a_202_);
v___x_204_ = l_Lean_Elab_Command_getScope___redArg(v___y_200_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_240_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_240_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_240_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_240_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v_openDecls_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_env_214_; lean_object* v_messages_215_; lean_object* v_scopes_216_; lean_object* v_usedQuotCtxts_217_; lean_object* v_nextMacroScope_218_; lean_object* v_maxRecDepth_219_; lean_object* v_ngen_220_; lean_object* v_auxDeclNGen_221_; lean_object* v_infoState_222_; lean_object* v_traceState_223_; lean_object* v_snapshotTasks_224_; lean_object* v_prevLinterStates_225_; lean_object* v_codeQualityEntryTasks_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_239_; 
v_openDecls_209_ = lean_ctor_get(v_a_205_, 3);
lean_inc(v_openDecls_209_);
lean_dec(v_a_205_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v_currNamespace_203_);
lean_ctor_set(v___x_210_, 1, v_openDecls_209_);
v___x_211_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___y_196_);
lean_inc_ref(v___y_193_);
lean_inc_ref(v___y_195_);
v___x_212_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_212_, 0, v___y_195_);
lean_ctor_set(v___x_212_, 1, v___y_197_);
lean_ctor_set(v___x_212_, 2, v___y_199_);
lean_ctor_set(v___x_212_, 3, v___y_193_);
lean_ctor_set(v___x_212_, 4, v___x_211_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*5, v___y_198_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*5 + 1, v___y_194_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*5 + 2, v_isSilent_188_);
v___x_213_ = lean_st_ref_take(v___y_200_);
v_env_214_ = lean_ctor_get(v___x_213_, 0);
v_messages_215_ = lean_ctor_get(v___x_213_, 1);
v_scopes_216_ = lean_ctor_get(v___x_213_, 2);
v_usedQuotCtxts_217_ = lean_ctor_get(v___x_213_, 3);
v_nextMacroScope_218_ = lean_ctor_get(v___x_213_, 4);
v_maxRecDepth_219_ = lean_ctor_get(v___x_213_, 5);
v_ngen_220_ = lean_ctor_get(v___x_213_, 6);
v_auxDeclNGen_221_ = lean_ctor_get(v___x_213_, 7);
v_infoState_222_ = lean_ctor_get(v___x_213_, 8);
v_traceState_223_ = lean_ctor_get(v___x_213_, 9);
v_snapshotTasks_224_ = lean_ctor_get(v___x_213_, 10);
v_prevLinterStates_225_ = lean_ctor_get(v___x_213_, 11);
v_codeQualityEntryTasks_226_ = lean_ctor_get(v___x_213_, 12);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_239_ == 0)
{
v___x_228_ = v___x_213_;
v_isShared_229_ = v_isSharedCheck_239_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_codeQualityEntryTasks_226_);
lean_inc(v_prevLinterStates_225_);
lean_inc(v_snapshotTasks_224_);
lean_inc(v_traceState_223_);
lean_inc(v_infoState_222_);
lean_inc(v_auxDeclNGen_221_);
lean_inc(v_ngen_220_);
lean_inc(v_maxRecDepth_219_);
lean_inc(v_nextMacroScope_218_);
lean_inc(v_usedQuotCtxts_217_);
lean_inc(v_scopes_216_);
lean_inc(v_messages_215_);
lean_inc(v_env_214_);
lean_dec(v___x_213_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_239_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = lean_box(0);
v___x_231_ = l_Lean_MessageLog_add(v___x_212_, v_messages_215_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 1, v___x_231_);
v___x_233_ = v___x_228_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_env_214_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_scopes_216_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_usedQuotCtxts_217_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_nextMacroScope_218_);
lean_ctor_set(v_reuseFailAlloc_238_, 5, v_maxRecDepth_219_);
lean_ctor_set(v_reuseFailAlloc_238_, 6, v_ngen_220_);
lean_ctor_set(v_reuseFailAlloc_238_, 7, v_auxDeclNGen_221_);
lean_ctor_set(v_reuseFailAlloc_238_, 8, v_infoState_222_);
lean_ctor_set(v_reuseFailAlloc_238_, 9, v_traceState_223_);
lean_ctor_set(v_reuseFailAlloc_238_, 10, v_snapshotTasks_224_);
lean_ctor_set(v_reuseFailAlloc_238_, 11, v_prevLinterStates_225_);
lean_ctor_set(v_reuseFailAlloc_238_, 12, v_codeQualityEntryTasks_226_);
v___x_233_ = v_reuseFailAlloc_238_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_st_ref_put(v___y_200_, v___x_233_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_230_);
v___x_236_ = v___x_207_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_230_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec(v_currNamespace_203_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_197_);
lean_dec_ref(v___y_196_);
v_a_241_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_204_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_204_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec(v___y_199_);
lean_dec_ref(v___y_197_);
lean_dec_ref(v___y_196_);
v_a_249_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_201_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_201_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
v___jp_257_:
{
lean_object* v_fileName_262_; lean_object* v_fileMap_263_; uint8_t v_suppressElabErrors_264_; lean_object* v___x_265_; lean_object* v___f_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_282_; 
v_fileName_262_ = lean_ctor_get(v___y_189_, 0);
v_fileMap_263_ = lean_ctor_get(v___y_189_, 1);
v_suppressElabErrors_264_ = lean_ctor_get_uint8(v___y_189_, sizeof(void*)*10);
v___x_265_ = lean_box(v_suppressElabErrors_264_);
v___f_266_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed), 2, 1);
lean_closure_set(v___f_266_, 0, v___x_265_);
v___x_267_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_186_);
v___x_268_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v___x_267_, v___y_190_);
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_282_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_282_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_282_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_inc_ref_n(v_fileMap_263_, 2);
v___x_273_ = l_Lean_FileMap_toPosition(v_fileMap_263_, v___y_259_);
lean_dec(v___y_259_);
v___x_274_ = l_Lean_FileMap_toPosition(v_fileMap_263_, v___y_261_);
lean_dec(v___y_261_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
v___x_276_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0));
if (v_suppressElabErrors_264_ == 0)
{
lean_del_object(v___x_271_);
lean_dec_ref(v___f_266_);
v___y_193_ = v___x_276_;
v___y_194_ = v___y_258_;
v___y_195_ = v_fileName_262_;
v___y_196_ = v_a_269_;
v___y_197_ = v___x_273_;
v___y_198_ = v___y_260_;
v___y_199_ = v___x_275_;
v___y_200_ = v___y_190_;
goto v___jp_192_;
}
else
{
uint8_t v___x_277_; 
lean_inc(v_a_269_);
v___x_277_ = l_Lean_MessageData_hasTag(v___f_266_, v_a_269_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_280_; 
lean_dec_ref_known(v___x_275_, 1);
lean_dec_ref(v___x_273_);
lean_dec(v_a_269_);
v___x_278_ = lean_box(0);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_278_);
v___x_280_ = v___x_271_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
else
{
lean_del_object(v___x_271_);
v___y_193_ = v___x_276_;
v___y_194_ = v___y_258_;
v___y_195_ = v_fileName_262_;
v___y_196_ = v_a_269_;
v___y_197_ = v___x_273_;
v___y_198_ = v___y_260_;
v___y_199_ = v___x_275_;
v___y_200_ = v___y_190_;
goto v___jp_192_;
}
}
}
}
v___jp_283_:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Syntax_getTailPos_x3f(v___y_285_, v___y_286_);
lean_dec(v___y_285_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_inc(v___y_287_);
v___y_258_ = v___y_284_;
v___y_259_ = v___y_287_;
v___y_260_ = v___y_286_;
v___y_261_ = v___y_287_;
goto v___jp_257_;
}
else
{
lean_object* v_val_289_; 
v_val_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_val_289_);
lean_dec_ref_known(v___x_288_, 1);
v___y_258_ = v___y_284_;
v___y_259_ = v___y_287_;
v___y_260_ = v___y_286_;
v___y_261_ = v_val_289_;
goto v___jp_257_;
}
}
v___jp_290_:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Elab_Command_getRef___redArg(v___y_189_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v_ref_295_; lean_object* v___x_296_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_a_294_);
lean_dec_ref_known(v___x_293_, 1);
v_ref_295_ = l_Lean_replaceRef(v_ref_185_, v_a_294_);
lean_dec(v_a_294_);
v___x_296_ = l_Lean_Syntax_getPos_x3f(v_ref_295_, v___y_291_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___y_284_ = v___y_292_;
v___y_285_ = v_ref_295_;
v___y_286_ = v___y_291_;
v___y_287_ = v___x_297_;
goto v___jp_283_;
}
else
{
lean_object* v_val_298_; 
v_val_298_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_val_298_);
lean_dec_ref_known(v___x_296_, 1);
v___y_284_ = v___y_292_;
v___y_285_ = v_ref_295_;
v___y_286_ = v___y_291_;
v___y_287_ = v_val_298_;
goto v___jp_283_;
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v_msgData_186_);
v_a_299_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_293_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_293_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
v___jp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_scopes_312_; lean_object* v___x_313_; lean_object* v_opts_314_; uint8_t v___x_315_; uint8_t v___x_316_; 
v___x_310_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_311_ = lean_st_ref_get(v___y_190_);
v_scopes_312_ = lean_ctor_get(v___x_311_, 2);
lean_inc(v_scopes_312_);
lean_dec(v___x_311_);
v___x_313_ = l_List_head_x21___redArg(v___x_310_, v_scopes_312_);
lean_dec(v_scopes_312_);
v_opts_314_ = lean_ctor_get(v___x_313_, 1);
lean_inc_ref(v_opts_314_);
lean_dec(v___x_313_);
v___x_315_ = 1;
v___x_316_ = l_Lean_instBEqMessageSeverity_beq(v_severity_187_, v___x_315_);
if (v___x_316_ == 0)
{
lean_dec_ref(v_opts_314_);
v___y_291_ = v___y_309_;
v___y_292_ = v_severity_187_;
goto v___jp_290_;
}
else
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = l_Lean_warningAsError;
v___x_318_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(v_opts_314_, v___x_317_);
lean_dec_ref(v_opts_314_);
if (v___x_318_ == 0)
{
v___y_291_ = v___y_309_;
v___y_292_ = v_severity_187_;
goto v___jp_290_;
}
else
{
v___y_291_ = v___y_309_;
v___y_292_ = v___x_307_;
goto v___jp_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_ref_323_, lean_object* v_msgData_324_, lean_object* v_severity_325_, lean_object* v_isSilent_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
uint8_t v_severity_boxed_330_; uint8_t v_isSilent_boxed_331_; lean_object* v_res_332_; 
v_severity_boxed_330_ = lean_unbox(v_severity_325_);
v_isSilent_boxed_331_ = lean_unbox(v_isSilent_326_);
v_res_332_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(v_ref_323_, v_msgData_324_, v_severity_boxed_330_, v_isSilent_boxed_331_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v_ref_323_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(lean_object* v_ref_333_, lean_object* v_msgData_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
uint8_t v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; 
v___x_338_ = 1;
v___x_339_ = 0;
v___x_340_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(v_ref_333_, v_msgData_334_, v___x_338_, v___x_339_, v___y_335_, v___y_336_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4___boxed(lean_object* v_ref_341_, lean_object* v_msgData_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(v_ref_341_, v_msgData_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v_ref_341_);
return v_res_346_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__0));
v___x_349_ = l_Lean_stringToMessageData(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__2));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(lean_object* v_linterOption_353_, lean_object* v_stx_354_, lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_name_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_377_; 
v_name_359_ = lean_ctor_get(v_linterOption_353_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v_linterOption_353_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v_linterOption_353_, 1);
lean_dec(v_unused_378_);
v___x_361_ = v_linterOption_353_;
v_isShared_362_ = v_isSharedCheck_377_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_name_359_);
lean_dec(v_linterOption_353_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_377_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1);
lean_inc(v_name_359_);
v___x_364_ = l_Lean_MessageData_ofName(v_name_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set_tag(v___x_361_, 7);
lean_ctor_set(v___x_361_, 1, v___x_364_);
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_376_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_disable_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_367_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3);
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v_disable_369_ = l_Lean_MessageData_note(v___x_368_);
v___x_370_ = l_Lean_Linter_linterMessageTag;
v___x_371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_371_, 0, v_msg_355_);
lean_ctor_set(v___x_371_, 1, v_disable_369_);
v___x_372_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_373_, 0, v_name_359_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
lean_inc(v_stx_354_);
v___x_374_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_374_, 0, v_stx_354_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(v_stx_354_, v___x_374_, v___y_356_, v___y_357_);
lean_dec(v_stx_354_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_379_, lean_object* v_stx_380_, lean_object* v_msg_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_379_, v_stx_380_, v_msg_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(lean_object* v_linterOption_386_, lean_object* v_stx_387_, lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_403_; 
v___x_392_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_389_, v___y_390_);
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_403_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_403_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_403_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
uint8_t v___x_397_; 
v___x_397_ = l_Lean_Linter_getLinterValue(v_linterOption_386_, v_a_393_);
lean_dec(v_a_393_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_400_; 
lean_dec_ref(v_msg_388_);
lean_dec(v_stx_387_);
lean_dec_ref(v_linterOption_386_);
v___x_398_ = lean_box(0);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
else
{
lean_object* v___x_402_; 
lean_del_object(v___x_395_);
v___x_402_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_386_, v_stx_387_, v_msg_388_, v___y_389_, v___y_390_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2___boxed(lean_object* v_linterOption_404_, lean_object* v_stx_405_, lean_object* v_msg_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(v_linterOption_404_, v_stx_405_, v_msg_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(lean_object* v___x_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Meta_isProp(v___x_411_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed(lean_object* v___x_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(v___x_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_428_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0));
v___x_431_ = l_Lean_stringToMessageData(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2));
v___x_434_ = l_Lean_stringToMessageData(v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(lean_object* v___x_435_, uint8_t v___x_436_, lean_object* v_as_x27_437_, lean_object* v_b_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
if (lean_obj_tag(v_as_x27_437_) == 0)
{
lean_object* v___x_442_; 
lean_dec_ref(v___x_435_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_b_438_);
return v___x_442_;
}
else
{
lean_object* v_head_443_; lean_object* v_tail_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_head_443_ = lean_ctor_get(v_as_x27_437_, 0);
v_tail_444_ = lean_ctor_get(v_as_x27_437_, 1);
v___x_445_ = lean_box(0);
lean_inc(v_head_443_);
lean_inc_ref(v___x_435_);
v___x_446_ = l_Lean_Environment_find_x3f(v___x_435_, v_head_443_, v___x_436_);
if (lean_obj_tag(v___x_446_) == 1)
{
lean_object* v_val_447_; uint8_t v___x_448_; 
v_val_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v___x_446_, 1);
v___x_448_ = l_Lean_ConstantInfo_isDefinition(v_val_447_);
if (v___x_448_ == 0)
{
lean_dec(v_val_447_);
v_as_x27_437_ = v_tail_444_;
v_b_438_ = v___x_445_;
goto _start;
}
else
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = l_Lean_ConstantInfo_hints(v_val_447_);
v___x_451_ = l_Lean_ReducibilityHints_isAbbrev(v___x_450_);
lean_dec(v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___f_454_; lean_object* v___x_455_; 
v___x_452_ = l_Lean_Linter_linter_defProp;
v___x_453_ = l_Lean_ConstantInfo_type(v_val_447_);
lean_dec(v_val_447_);
v___f_454_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_454_, 0, v___x_453_);
v___x_455_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_454_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; uint8_t v___x_457_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = lean_unbox(v_a_456_);
lean_dec(v_a_456_);
if (v___x_457_ == 0)
{
v_as_x27_437_ = v_tail_444_;
v_b_438_ = v___x_445_;
goto _start;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Elab_Command_getRef___redArg(v___y_439_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1);
lean_inc(v_head_443_);
v___x_462_ = l_Lean_MessageData_ofConstName(v_head_443_, v___x_451_);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(v___x_452_, v_a_460_, v___x_465_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_dec_ref_known(v___x_466_, 1);
v_as_x27_437_ = v_tail_444_;
v_b_438_ = v___x_445_;
goto _start;
}
else
{
lean_dec_ref(v___x_435_);
return v___x_466_;
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec_ref(v___x_435_);
v_a_468_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_459_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_459_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v___x_435_);
v_a_476_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_455_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_455_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_dec(v_val_447_);
v_as_x27_437_ = v_tail_444_;
v_b_438_ = v___x_445_;
goto _start;
}
}
}
else
{
lean_dec(v___x_446_);
v_as_x27_437_ = v_tail_444_;
v_b_438_ = v___x_445_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___boxed(lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v_as_x27_488_, lean_object* v_b_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
uint8_t v___x_8958__boxed_493_; lean_object* v_res_494_; 
v___x_8958__boxed_493_ = lean_unbox(v___x_487_);
v_res_494_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_486_, v___x_8958__boxed_493_, v_as_x27_488_, v_b_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v_as_x27_488_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(lean_object* v___x_498_, uint8_t v___x_499_, lean_object* v_as_500_, size_t v_sz_501_, size_t v_i_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_502_, v_sz_501_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec_ref(v___x_498_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v_b_503_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v_a_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec_ref(v_b_503_);
v___x_509_ = lean_box(0);
v_a_510_ = lean_array_uget_borrowed(v_as_500_, v_i_502_);
lean_inc(v_a_510_);
v___x_511_ = l_Lean_Linter_getDeclsByBody(v_a_510_);
lean_inc_ref(v___x_498_);
v___x_512_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_498_, v___x_499_, v___x_511_, v___x_509_, v___y_504_, v___y_505_);
lean_dec(v___x_511_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v___x_513_; size_t v___x_514_; size_t v___x_515_; 
lean_dec_ref_known(v___x_512_, 1);
v___x_513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0));
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_add(v_i_502_, v___x_514_);
v_i_502_ = v___x_515_;
v_b_503_ = v___x_513_;
goto _start;
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v___x_498_);
v_a_517_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_512_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_512_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___boxed(lean_object* v___x_525_, lean_object* v___x_526_, lean_object* v_as_527_, lean_object* v_sz_528_, lean_object* v_i_529_, lean_object* v_b_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
uint8_t v___x_9075__boxed_534_; size_t v_sz_boxed_535_; size_t v_i_boxed_536_; lean_object* v_res_537_; 
v___x_9075__boxed_534_ = lean_unbox(v___x_526_);
v_sz_boxed_535_ = lean_unbox_usize(v_sz_528_);
lean_dec(v_sz_528_);
v_i_boxed_536_ = lean_unbox_usize(v_i_529_);
lean_dec(v_i_529_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_525_, v___x_9075__boxed_534_, v_as_527_, v_sz_boxed_535_, v_i_boxed_536_, v_b_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v_as_527_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(lean_object* v___x_538_, uint8_t v___x_539_, lean_object* v_as_540_, size_t v_sz_541_, size_t v_i_542_, lean_object* v_b_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = lean_usize_dec_lt(v_i_542_, v_sz_541_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec_ref(v___x_538_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v_b_543_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_dec_ref(v_b_543_);
v___x_549_ = lean_box(0);
v_a_550_ = lean_array_uget_borrowed(v_as_540_, v_i_542_);
lean_inc(v_a_550_);
v___x_551_ = l_Lean_Linter_getDeclsByBody(v_a_550_);
lean_inc_ref(v___x_538_);
v___x_552_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_538_, v___x_539_, v___x_551_, v___x_549_, v___y_544_, v___y_545_);
lean_dec(v___x_551_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_553_; size_t v___x_554_; size_t v___x_555_; lean_object* v___x_556_; 
lean_dec_ref_known(v___x_552_, 1);
v___x_553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0));
v___x_554_ = ((size_t)1ULL);
v___x_555_ = lean_usize_add(v_i_542_, v___x_554_);
v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_538_, v___x_539_, v_as_540_, v_sz_541_, v___x_555_, v___x_553_, v___y_544_, v___y_545_);
return v___x_556_;
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref(v___x_538_);
v_a_557_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_552_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_552_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9___boxed(lean_object* v___x_565_, lean_object* v___x_566_, lean_object* v_as_567_, lean_object* v_sz_568_, lean_object* v_i_569_, lean_object* v_b_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
uint8_t v___x_9131__boxed_574_; size_t v_sz_boxed_575_; size_t v_i_boxed_576_; lean_object* v_res_577_; 
v___x_9131__boxed_574_ = lean_unbox(v___x_566_);
v_sz_boxed_575_ = lean_unbox_usize(v_sz_568_);
lean_dec(v_sz_568_);
v_i_boxed_576_ = lean_unbox_usize(v_i_569_);
lean_dec(v_i_569_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_565_, v___x_9131__boxed_574_, v_as_567_, v_sz_boxed_575_, v_i_boxed_576_, v_b_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v_as_567_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(lean_object* v_init_578_, lean_object* v___x_579_, uint8_t v___x_580_, lean_object* v_n_581_, lean_object* v_b_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
if (lean_obj_tag(v_n_581_) == 0)
{
lean_object* v_cs_586_; lean_object* v___x_587_; lean_object* v___x_588_; size_t v_sz_589_; size_t v___x_590_; lean_object* v___x_591_; 
v_cs_586_ = lean_ctor_get(v_n_581_, 0);
v___x_587_ = lean_box(0);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_b_582_);
v_sz_589_ = lean_array_size(v_cs_586_);
v___x_590_ = ((size_t)0ULL);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_578_, v___x_579_, v___x_580_, v_cs_586_, v_sz_589_, v___x_590_, v___x_588_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_606_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_606_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_fst_596_; 
v_fst_596_ = lean_ctor_get(v_a_592_, 0);
if (lean_obj_tag(v_fst_596_) == 0)
{
lean_object* v_snd_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v_snd_597_ = lean_ctor_get(v_a_592_, 1);
lean_inc(v_snd_597_);
lean_dec(v_a_592_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_snd_597_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_598_);
v___x_600_ = v___x_594_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
else
{
lean_object* v_val_602_; lean_object* v___x_604_; 
lean_inc_ref(v_fst_596_);
lean_dec(v_a_592_);
v_val_602_ = lean_ctor_get(v_fst_596_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v_fst_596_, 1);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v_val_602_);
v___x_604_ = v___x_594_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_val_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_a_607_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_591_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_591_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_object* v_vs_615_; lean_object* v___x_616_; lean_object* v___x_617_; size_t v_sz_618_; size_t v___x_619_; lean_object* v___x_620_; 
v_vs_615_ = lean_ctor_get(v_n_581_, 0);
v___x_616_ = lean_box(0);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v_b_582_);
v_sz_618_ = lean_array_size(v_vs_615_);
v___x_619_ = ((size_t)0ULL);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_579_, v___x_580_, v_vs_615_, v_sz_618_, v___x_619_, v___x_617_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_635_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_635_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_635_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_635_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_fst_625_; 
v_fst_625_ = lean_ctor_get(v_a_621_, 0);
if (lean_obj_tag(v_fst_625_) == 0)
{
lean_object* v_snd_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
v_snd_626_ = lean_ctor_get(v_a_621_, 1);
lean_inc(v_snd_626_);
lean_dec(v_a_621_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v_snd_626_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_627_);
v___x_629_ = v___x_623_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
else
{
lean_object* v_val_631_; lean_object* v___x_633_; 
lean_inc_ref(v_fst_625_);
lean_dec(v_a_621_);
v_val_631_ = lean_ctor_get(v_fst_625_, 0);
lean_inc(v_val_631_);
lean_dec_ref_known(v_fst_625_, 1);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v_val_631_);
v___x_633_ = v___x_623_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_val_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
v_a_636_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_620_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_620_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(lean_object* v_init_644_, lean_object* v___x_645_, uint8_t v___x_646_, lean_object* v_as_647_, size_t v_sz_648_, size_t v_i_649_, lean_object* v_b_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
uint8_t v___x_654_; 
v___x_654_ = lean_usize_dec_lt(v_i_649_, v_sz_648_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec_ref(v___x_645_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_b_650_);
return v___x_655_;
}
else
{
lean_object* v_snd_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_690_; 
v_snd_656_ = lean_ctor_get(v_b_650_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_b_650_);
if (v_isSharedCheck_690_ == 0)
{
lean_object* v_unused_691_; 
v_unused_691_ = lean_ctor_get(v_b_650_, 0);
lean_dec(v_unused_691_);
v___x_658_ = v_b_650_;
v_isShared_659_ = v_isSharedCheck_690_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_snd_656_);
lean_dec(v_b_650_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_690_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v_a_661_; lean_object* v___x_662_; 
v___x_660_ = lean_box(0);
v_a_661_ = lean_array_uget_borrowed(v_as_647_, v_i_649_);
lean_inc(v_snd_656_);
lean_inc_ref(v___x_645_);
v___x_662_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_644_, v___x_645_, v___x_646_, v_a_661_, v_snd_656_, v___y_651_, v___y_652_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_681_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_681_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_681_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_681_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
if (lean_obj_tag(v_a_663_) == 0)
{
lean_object* v___x_667_; lean_object* v___x_669_; 
lean_dec_ref(v___x_645_);
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v_a_663_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_667_);
v___x_669_ = v___x_658_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_snd_656_);
v___x_669_ = v_reuseFailAlloc_673_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_671_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_669_);
v___x_671_ = v___x_665_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; 
lean_del_object(v___x_665_);
lean_dec(v_snd_656_);
v_a_674_ = lean_ctor_get(v_a_663_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v_a_663_, 1);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v_a_674_);
lean_ctor_set(v___x_658_, 0, v___x_660_);
v___x_676_ = v___x_658_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_a_674_);
v___x_676_ = v_reuseFailAlloc_680_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
size_t v___x_677_; size_t v___x_678_; 
v___x_677_ = ((size_t)1ULL);
v___x_678_ = lean_usize_add(v_i_649_, v___x_677_);
v_i_649_ = v___x_678_;
v_b_650_ = v___x_676_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_del_object(v___x_658_);
lean_dec(v_snd_656_);
lean_dec_ref(v___x_645_);
v_a_682_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_662_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_662_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8___boxed(lean_object* v_init_692_, lean_object* v___x_693_, lean_object* v___x_694_, lean_object* v_as_695_, lean_object* v_sz_696_, lean_object* v_i_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
uint8_t v___x_9182__boxed_702_; size_t v_sz_boxed_703_; size_t v_i_boxed_704_; lean_object* v_res_705_; 
v___x_9182__boxed_702_ = lean_unbox(v___x_694_);
v_sz_boxed_703_ = lean_unbox_usize(v_sz_696_);
lean_dec(v_sz_696_);
v_i_boxed_704_ = lean_unbox_usize(v_i_697_);
lean_dec(v_i_697_);
v_res_705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_692_, v___x_693_, v___x_9182__boxed_702_, v_as_695_, v_sz_boxed_703_, v_i_boxed_704_, v_b_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v_as_695_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6___boxed(lean_object* v_init_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v_n_709_, lean_object* v_b_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
uint8_t v___x_9203__boxed_714_; lean_object* v_res_715_; 
v___x_9203__boxed_714_ = lean_unbox(v___x_708_);
v_res_715_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_706_, v___x_707_, v___x_9203__boxed_714_, v_n_709_, v_b_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v_n_709_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(lean_object* v___x_719_, uint8_t v___x_720_, lean_object* v_as_721_, size_t v_sz_722_, size_t v_i_723_, lean_object* v_b_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = lean_usize_dec_lt(v_i_723_, v_sz_722_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec_ref(v___x_719_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v_b_724_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; lean_object* v_a_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref(v_b_724_);
v___x_730_ = lean_box(0);
v_a_731_ = lean_array_uget_borrowed(v_as_721_, v_i_723_);
lean_inc(v_a_731_);
v___x_732_ = l_Lean_Linter_getDeclsByBody(v_a_731_);
lean_inc_ref(v___x_719_);
v___x_733_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_719_, v___x_720_, v___x_732_, v___x_730_, v___y_725_, v___y_726_);
lean_dec(v___x_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; size_t v___x_735_; size_t v___x_736_; 
lean_dec_ref_known(v___x_733_, 1);
v___x_734_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0));
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_add(v_i_723_, v___x_735_);
v_i_723_ = v___x_736_;
v_b_724_ = v___x_734_;
goto _start;
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v___x_719_);
v_a_738_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_733_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_733_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___boxed(lean_object* v___x_746_, lean_object* v___x_747_, lean_object* v_as_748_, lean_object* v_sz_749_, lean_object* v_i_750_, lean_object* v_b_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
uint8_t v___x_9395__boxed_755_; size_t v_sz_boxed_756_; size_t v_i_boxed_757_; lean_object* v_res_758_; 
v___x_9395__boxed_755_ = lean_unbox(v___x_747_);
v_sz_boxed_756_ = lean_unbox_usize(v_sz_749_);
lean_dec(v_sz_749_);
v_i_boxed_757_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_746_, v___x_9395__boxed_755_, v_as_748_, v_sz_boxed_756_, v_i_boxed_757_, v_b_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec_ref(v_as_748_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(lean_object* v___x_759_, uint8_t v___x_760_, lean_object* v_as_761_, size_t v_sz_762_, size_t v_i_763_, lean_object* v_b_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
uint8_t v___x_768_; 
v___x_768_ = lean_usize_dec_lt(v_i_763_, v_sz_762_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec_ref(v___x_759_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v_b_764_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref(v_b_764_);
v___x_770_ = lean_box(0);
v_a_771_ = lean_array_uget_borrowed(v_as_761_, v_i_763_);
lean_inc(v_a_771_);
v___x_772_ = l_Lean_Linter_getDeclsByBody(v_a_771_);
lean_inc_ref(v___x_759_);
v___x_773_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_759_, v___x_760_, v___x_772_, v___x_770_, v___y_765_, v___y_766_);
lean_dec(v___x_772_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v___x_774_; size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; 
lean_dec_ref_known(v___x_773_, 1);
v___x_774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0));
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_add(v_i_763_, v___x_775_);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_759_, v___x_760_, v_as_761_, v_sz_762_, v___x_776_, v___x_774_, v___y_765_, v___y_766_);
return v___x_777_;
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v___x_759_);
v_a_778_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_773_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_773_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7___boxed(lean_object* v___x_786_, lean_object* v___x_787_, lean_object* v_as_788_, lean_object* v_sz_789_, lean_object* v_i_790_, lean_object* v_b_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
uint8_t v___x_9451__boxed_795_; size_t v_sz_boxed_796_; size_t v_i_boxed_797_; lean_object* v_res_798_; 
v___x_9451__boxed_795_ = lean_unbox(v___x_787_);
v_sz_boxed_796_ = lean_unbox_usize(v_sz_789_);
lean_dec(v_sz_789_);
v_i_boxed_797_ = lean_unbox_usize(v_i_790_);
lean_dec(v_i_790_);
v_res_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_786_, v___x_9451__boxed_795_, v_as_788_, v_sz_boxed_796_, v_i_boxed_797_, v_b_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v_as_788_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(lean_object* v___x_799_, uint8_t v___x_800_, lean_object* v_t_801_, lean_object* v_init_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_root_806_; lean_object* v_tail_807_; lean_object* v___x_808_; 
v_root_806_ = lean_ctor_get(v_t_801_, 0);
v_tail_807_ = lean_ctor_get(v_t_801_, 1);
lean_inc_ref(v___x_799_);
v___x_808_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_802_, v___x_799_, v___x_800_, v_root_806_, v_init_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_845_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_845_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_845_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_845_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
if (lean_obj_tag(v_a_809_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; 
lean_dec_ref(v___x_799_);
v_a_813_ = lean_ctor_get(v_a_809_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v_a_809_, 1);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_a_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_818_; lean_object* v___x_819_; size_t v_sz_820_; size_t v___x_821_; lean_object* v___x_822_; 
lean_del_object(v___x_811_);
v_a_817_ = lean_ctor_get(v_a_809_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v_a_809_, 1);
v___x_818_ = lean_box(0);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
lean_ctor_set(v___x_819_, 1, v_a_817_);
v_sz_820_ = lean_array_size(v_tail_807_);
v___x_821_ = ((size_t)0ULL);
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_799_, v___x_800_, v_tail_807_, v_sz_820_, v___x_821_, v___x_819_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_836_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_836_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_836_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_836_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_fst_827_; 
v_fst_827_ = lean_ctor_get(v_a_823_, 0);
if (lean_obj_tag(v_fst_827_) == 0)
{
lean_object* v_snd_828_; lean_object* v___x_830_; 
v_snd_828_ = lean_ctor_get(v_a_823_, 1);
lean_inc(v_snd_828_);
lean_dec(v_a_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v_snd_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_snd_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v_val_832_; lean_object* v___x_834_; 
lean_inc_ref(v_fst_827_);
lean_dec(v_a_823_);
v_val_832_ = lean_ctor_get(v_fst_827_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v_fst_827_, 1);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v_val_832_);
v___x_834_ = v___x_825_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_val_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_837_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_822_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_822_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec_ref(v___x_799_);
v_a_846_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_808_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_808_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4___boxed(lean_object* v___x_854_, lean_object* v___x_855_, lean_object* v_t_856_, lean_object* v_init_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
uint8_t v___x_9502__boxed_861_; lean_object* v_res_862_; 
v___x_9502__boxed_861_ = lean_unbox(v___x_855_);
v_res_862_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(v___x_854_, v___x_9502__boxed_861_, v_t_856_, v_init_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v_t_856_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DefProp_defPropLinter___lam__0(lean_object* v_x_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_899_; 
v___x_867_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_864_, v___y_865_);
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_899_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_899_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_899_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = l_Lean_Linter_linter_defProp;
v___x_873_ = l_Lean_Linter_getLinterValue(v___x_872_, v_a_868_);
lean_dec(v_a_868_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = lean_box(0);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_874_);
v___x_876_ = v___x_870_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
lean_object* v___x_878_; lean_object* v_messages_879_; uint8_t v___x_880_; 
v___x_878_ = lean_st_ref_get(v___y_865_);
v_messages_879_ = lean_ctor_get(v___x_878_, 1);
lean_inc_ref(v_messages_879_);
lean_dec(v___x_878_);
v___x_880_ = l_Lean_MessageLog_hasErrors(v_messages_879_);
lean_dec_ref(v_messages_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v_env_882_; lean_object* v___x_883_; lean_object* v_a_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
lean_del_object(v___x_870_);
v___x_881_ = lean_st_ref_get(v___y_865_);
v_env_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc_ref(v_env_882_);
lean_dec(v___x_881_);
v___x_883_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(v___y_865_);
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_883_);
v___x_885_ = lean_box(0);
v___x_886_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(v_env_882_, v___x_880_, v_a_884_, v___x_885_, v___y_864_, v___y_865_);
lean_dec(v_a_884_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v___x_886_, 0);
lean_dec(v_unused_894_);
v___x_888_ = v___x_886_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_dec(v___x_886_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_885_);
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_885_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
else
{
return v___x_886_;
}
}
else
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_895_);
v___x_897_ = v___x_870_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DefProp_defPropLinter___lam__0___boxed(lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Linter_DefProp_defPropLinter___lam__0(v_x_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v_x_900_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(lean_object* v_o_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_o_919_, v___y_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___boxed(lean_object* v_o_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(v_o_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(lean_object* v___x_929_, uint8_t v___x_930_, lean_object* v_as_931_, lean_object* v_as_x27_932_, lean_object* v_b_933_, lean_object* v_a_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_929_, v___x_930_, v_as_x27_932_, v_b_933_, v___y_935_, v___y_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___boxed(lean_object* v___x_939_, lean_object* v___x_940_, lean_object* v_as_941_, lean_object* v_as_x27_942_, lean_object* v_b_943_, lean_object* v_a_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
uint8_t v___x_9735__boxed_948_; lean_object* v_res_949_; 
v___x_9735__boxed_948_ = lean_unbox(v___x_940_);
v_res_949_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(v___x_939_, v___x_9735__boxed_948_, v_as_941_, v_as_x27_942_, v_b_943_, v_a_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v_as_x27_942_);
lean_dec(v_as_941_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_msgData_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_msgData_950_, v___y_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_msgData_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(v_msgData_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_Linter_DefProp_defPropLinter));
v___x_962_ = l_Lean_Elab_Command_addLinter(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2____boxed(lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_();
return v_res_964_;
}
}
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_DefProp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_defProp = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_defProp);
lean_dec_ref(res);
res = l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_DefProp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_DefProp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_DefProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_DefProp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_DefProp(builtin);
}
#ifdef __cplusplus
}
#endif
