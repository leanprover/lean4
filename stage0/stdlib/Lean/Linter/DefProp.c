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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_814211969____hygCtx___hyg_4_();
return v_res_60_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; lean_object* v_infoState_64_; lean_object* v_trees_65_; lean_object* v___x_66_; 
v___x_63_ = lean_st_ref_get(v___y_61_);
v_infoState_64_ = lean_ctor_get(v___x_63_, 8);
lean_inc_ref(v_infoState_64_);
lean_dec(v___x_63_);
v_trees_65_ = lean_ctor_get(v_infoState_64_, 2);
lean_inc_ref(v_trees_65_);
lean_dec_ref(v_infoState_64_);
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v_trees_65_);
return v___x_66_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_61_ = stack[0].m_obj;
lean_object* v_res_67_;
v_res_67_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(v___y_61_);
stack->m_obj
 = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg___boxed(lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(v___y_68_);
lean_dec(v___y_68_);
return v_res_70_;
}
}
lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1(lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(v___y_72_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_71_ = stack[0].m_obj;
lean_object* v___y_72_ = stack[1].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1(v___y_71_, v___y_72_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___boxed(lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1(v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_79_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(lean_object* v_o_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v_env_85_; lean_object* v___x_86_; lean_object* v_toEnvExtension_87_; lean_object* v_asyncMode_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v_merged_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v___x_83_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_84_ = lean_st_ref_get(v___y_81_);
v_env_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc_ref(v_env_85_);
lean_dec(v___x_84_);
v___x_86_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_87_ = lean_ctor_get(v___x_86_, 0);
v_asyncMode_88_ = lean_ctor_get(v_toEnvExtension_87_, 2);
v___x_89_ = lean_box(0);
v___x_90_ = 0;
v___x_91_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_83_, v___x_86_, v_env_85_, v_asyncMode_88_, v___x_89_, v___x_90_);
v_merged_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_91_, 1);
lean_dec(v_unused_101_);
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_merged_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 1, v_merged_92_);
lean_ctor_set(v___x_94_, 0, v_o_80_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_o_80_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_merged_92_);
v___x_97_ = v_reuseFailAlloc_99_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_80_ = stack[0].m_obj;
lean_object* v___y_81_ = stack[1].m_obj;
lean_object* v_res_102_;
v_res_102_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_o_80_, v___y_81_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_o_103_, v___y_104_);
lean_dec(v___y_104_);
return v_res_106_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_scopes_112_; lean_object* v___x_113_; lean_object* v_opts_114_; lean_object* v___x_115_; 
v___x_110_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_111_ = lean_st_ref_get(v___y_108_);
v_scopes_112_ = lean_ctor_get(v___x_111_, 2);
lean_inc(v_scopes_112_);
lean_dec(v___x_111_);
v___x_113_ = l_List_head_x21___redArg(v___x_110_, v_scopes_112_);
lean_dec(v_scopes_112_);
v_opts_114_ = lean_ctor_get(v___x_113_, 1);
lean_inc_ref(v_opts_114_);
lean_dec(v___x_113_);
v___x_115_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_opts_114_, v___y_108_);
return v___x_115_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_107_ = stack[0].m_obj;
lean_object* v___y_108_ = stack[1].m_obj;
lean_object* v_res_116_;
v_res_116_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_107_, v___y_108_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0___boxed(lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_120_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_121_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0);
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_124_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
lean_ctor_set(v___x_127_, 2, v___x_126_);
lean_ctor_set(v___x_127_, 3, v___x_126_);
lean_ctor_set(v___x_127_, 4, v___x_125_);
lean_ctor_set(v___x_127_, 5, v___x_125_);
lean_ctor_set(v___x_127_, 6, v___x_125_);
lean_ctor_set(v___x_127_, 7, v___x_125_);
lean_ctor_set(v___x_127_, 8, v___x_125_);
lean_ctor_set(v___x_127_, 9, v___x_125_);
lean_ctor_set(v___x_127_, 10, v___x_125_);
lean_ctor_set(v___x_127_, 11, v___x_124_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(32u);
v___x_129_ = lean_mk_empty_array_with_capacity(v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_131_ = ((size_t)5ULL);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_unsigned_to_nat(32u);
v___x_134_ = lean_mk_empty_array_with_capacity(v___x_133_);
v___x_135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3);
v___x_136_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_132_);
lean_ctor_set(v___x_136_, 3, v___x_132_);
lean_ctor_set_usize(v___x_136_, 4, v___x_131_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = lean_box(1);
v___x_138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4);
v___x_139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1);
v___x_140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_137_);
return v___x_140_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_msgData_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___x_144_; lean_object* v_env_145_; uint8_t v___x_146_; lean_object* v_env_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_scopes_150_; lean_object* v___x_151_; lean_object* v_opts_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_144_ = lean_st_ref_get(v___y_142_);
v_env_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc_ref(v_env_145_);
lean_dec(v___x_144_);
v___x_146_ = 0;
v_env_147_ = l_Lean_Environment_setRecordingDeps(v_env_145_, v___x_146_);
v___x_148_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_149_ = lean_st_ref_get(v___y_142_);
v_scopes_150_ = lean_ctor_get(v___x_149_, 2);
lean_inc(v_scopes_150_);
lean_dec(v___x_149_);
v___x_151_ = l_List_head_x21___redArg(v___x_148_, v_scopes_150_);
lean_dec(v_scopes_150_);
v_opts_152_ = lean_ctor_get(v___x_151_, 1);
lean_inc_ref(v_opts_152_);
lean_dec(v___x_151_);
v___x_153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2);
v___x_154_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5);
v___x_155_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_155_, 0, v_env_147_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_154_);
lean_ctor_set(v___x_155_, 3, v_opts_152_);
v___x_156_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_msgData_141_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_141_ = stack[0].m_obj;
lean_object* v___y_142_ = stack[1].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_msgData_141_, v___y_142_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_msgData_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_msgData_159_, v___y_160_);
lean_dec(v___y_160_);
return v_res_162_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(uint8_t v_suppressElabErrors_164_, uint8_t v___y_165_, lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 1)
{
lean_object* v_pre_167_; 
v_pre_167_ = lean_ctor_get(v_x_166_, 0);
if (lean_obj_tag(v_pre_167_) == 0)
{
lean_object* v_str_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v_str_168_ = lean_ctor_get(v_x_166_, 1);
v___x_169_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0));
v___x_170_ = lean_string_dec_eq(v_str_168_, v___x_169_);
if (v___x_170_ == 0)
{
return v___x_170_;
}
else
{
return v_suppressElabErrors_164_;
}
}
else
{
return v___y_165_;
}
}
else
{
return v___y_165_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_164_ = stack[0].m_num;
uint8_t v___y_165_ = stack[1].m_num;
lean_object* v_x_166_ = stack[2].m_obj;
uint8_t v_res_171_;
v_res_171_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(v_suppressElabErrors_164_, v___y_165_, v_x_166_);
stack->m_num = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed(lean_object* v_suppressElabErrors_172_, lean_object* v___y_173_, lean_object* v_x_174_){
_start:
{
uint8_t v_suppressElabErrors_boxed_175_; uint8_t v___y_8611__boxed_176_; uint8_t v_res_177_; lean_object* v_r_178_; 
v_suppressElabErrors_boxed_175_ = lean_unbox(v_suppressElabErrors_172_);
v___y_8611__boxed_176_ = lean_unbox(v___y_173_);
v_res_177_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(v_suppressElabErrors_boxed_175_, v___y_8611__boxed_176_, v_x_174_);
lean_dec(v_x_174_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(lean_object* v_opts_179_, lean_object* v_opt_180_){
_start:
{
lean_object* v_name_181_; lean_object* v_defValue_182_; lean_object* v_map_183_; lean_object* v___x_184_; 
v_name_181_ = lean_ctor_get(v_opt_180_, 0);
v_defValue_182_ = lean_ctor_get(v_opt_180_, 1);
v_map_183_ = lean_ctor_get(v_opts_179_, 0);
v___x_184_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_183_, v_name_181_);
if (lean_obj_tag(v___x_184_) == 0)
{
uint8_t v___x_185_; 
v___x_185_ = lean_unbox(v_defValue_182_);
return v___x_185_;
}
else
{
lean_object* v_val_186_; 
v_val_186_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_val_186_);
lean_dec_ref_known(v___x_184_, 1);
if (lean_obj_tag(v_val_186_) == 1)
{
uint8_t v_v_187_; 
v_v_187_ = lean_ctor_get_uint8(v_val_186_, 0);
lean_dec_ref_known(v_val_186_, 0);
return v_v_187_;
}
else
{
uint8_t v___x_188_; 
lean_dec(v_val_186_);
v___x_188_ = lean_unbox(v_defValue_182_);
return v___x_188_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_179_ = stack[0].m_obj;
lean_object* v_opt_180_ = stack[1].m_obj;
uint8_t v_res_189_;
v_res_189_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(v_opts_179_, v_opt_180_);
stack->m_num = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_opts_190_, lean_object* v_opt_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(v_opts_190_, v_opt_191_);
lean_dec_ref(v_opt_191_);
lean_dec_ref(v_opts_190_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(lean_object* v_ref_195_, lean_object* v_msgData_196_, uint8_t v_severity_197_, uint8_t v_isSilent_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___y_203_; uint8_t v___y_204_; lean_object* v___y_205_; uint8_t v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; uint8_t v___y_268_; uint8_t v___y_269_; uint8_t v___y_270_; lean_object* v___y_271_; lean_object* v___y_272_; uint8_t v___y_296_; uint8_t v___y_297_; lean_object* v___y_298_; uint8_t v___y_299_; lean_object* v___y_300_; uint8_t v___y_304_; uint8_t v___y_305_; uint8_t v___y_306_; uint8_t v___x_321_; uint8_t v___y_323_; uint8_t v___y_324_; uint8_t v___y_325_; uint8_t v___y_327_; uint8_t v___x_339_; 
v___x_321_ = 2;
v___x_339_ = l_Lean_instBEqMessageSeverity_beq(v_severity_197_, v___x_321_);
if (v___x_339_ == 0)
{
v___y_327_ = v___x_339_;
goto v___jp_326_;
}
else
{
uint8_t v___x_340_; 
lean_inc_ref(v_msgData_196_);
v___x_340_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_196_);
v___y_327_ = v___x_340_;
goto v___jp_326_;
}
v___jp_202_:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Elab_Command_getScope___redArg(v___y_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v_currNamespace_213_; lean_object* v___x_214_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v_currNamespace_213_ = lean_ctor_get(v_a_212_, 2);
lean_inc(v_currNamespace_213_);
lean_dec(v_a_212_);
v___x_214_ = l_Lean_Elab_Command_getScope___redArg(v___y_210_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_250_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_250_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_250_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_250_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_openDecls_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_env_224_; lean_object* v_messages_225_; lean_object* v_scopes_226_; lean_object* v_usedQuotCtxts_227_; lean_object* v_nextMacroScope_228_; lean_object* v_maxRecDepth_229_; lean_object* v_ngen_230_; lean_object* v_auxDeclNGen_231_; lean_object* v_infoState_232_; lean_object* v_traceState_233_; lean_object* v_snapshotTasks_234_; lean_object* v_prevLinterStates_235_; lean_object* v_codeQualityEntryTasks_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_249_; 
v_openDecls_219_ = lean_ctor_get(v_a_215_, 3);
lean_inc(v_openDecls_219_);
lean_dec(v_a_215_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v_currNamespace_213_);
lean_ctor_set(v___x_220_, 1, v_openDecls_219_);
v___x_221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc_ref(v___y_209_);
v___x_222_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_222_, 0, v___y_209_);
lean_ctor_set(v___x_222_, 1, v___y_203_);
lean_ctor_set(v___x_222_, 2, v___y_205_);
lean_ctor_set(v___x_222_, 3, v___y_207_);
lean_ctor_set(v___x_222_, 4, v___x_221_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*5, v___y_204_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*5 + 1, v___y_206_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*5 + 2, v_isSilent_198_);
v___x_223_ = lean_st_ref_take(v___y_210_);
v_env_224_ = lean_ctor_get(v___x_223_, 0);
v_messages_225_ = lean_ctor_get(v___x_223_, 1);
v_scopes_226_ = lean_ctor_get(v___x_223_, 2);
v_usedQuotCtxts_227_ = lean_ctor_get(v___x_223_, 3);
v_nextMacroScope_228_ = lean_ctor_get(v___x_223_, 4);
v_maxRecDepth_229_ = lean_ctor_get(v___x_223_, 5);
v_ngen_230_ = lean_ctor_get(v___x_223_, 6);
v_auxDeclNGen_231_ = lean_ctor_get(v___x_223_, 7);
v_infoState_232_ = lean_ctor_get(v___x_223_, 8);
v_traceState_233_ = lean_ctor_get(v___x_223_, 9);
v_snapshotTasks_234_ = lean_ctor_get(v___x_223_, 10);
v_prevLinterStates_235_ = lean_ctor_get(v___x_223_, 11);
v_codeQualityEntryTasks_236_ = lean_ctor_get(v___x_223_, 12);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_249_ == 0)
{
v___x_238_ = v___x_223_;
v_isShared_239_ = v_isSharedCheck_249_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_codeQualityEntryTasks_236_);
lean_inc(v_prevLinterStates_235_);
lean_inc(v_snapshotTasks_234_);
lean_inc(v_traceState_233_);
lean_inc(v_infoState_232_);
lean_inc(v_auxDeclNGen_231_);
lean_inc(v_ngen_230_);
lean_inc(v_maxRecDepth_229_);
lean_inc(v_nextMacroScope_228_);
lean_inc(v_usedQuotCtxts_227_);
lean_inc(v_scopes_226_);
lean_inc(v_messages_225_);
lean_inc(v_env_224_);
lean_dec(v___x_223_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_249_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_240_ = lean_box(0);
v___x_241_ = l_Lean_MessageLog_add(v___x_222_, v_messages_225_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v___x_241_);
v___x_243_ = v___x_238_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_env_224_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_248_, 2, v_scopes_226_);
lean_ctor_set(v_reuseFailAlloc_248_, 3, v_usedQuotCtxts_227_);
lean_ctor_set(v_reuseFailAlloc_248_, 4, v_nextMacroScope_228_);
lean_ctor_set(v_reuseFailAlloc_248_, 5, v_maxRecDepth_229_);
lean_ctor_set(v_reuseFailAlloc_248_, 6, v_ngen_230_);
lean_ctor_set(v_reuseFailAlloc_248_, 7, v_auxDeclNGen_231_);
lean_ctor_set(v_reuseFailAlloc_248_, 8, v_infoState_232_);
lean_ctor_set(v_reuseFailAlloc_248_, 9, v_traceState_233_);
lean_ctor_set(v_reuseFailAlloc_248_, 10, v_snapshotTasks_234_);
lean_ctor_set(v_reuseFailAlloc_248_, 11, v_prevLinterStates_235_);
lean_ctor_set(v_reuseFailAlloc_248_, 12, v_codeQualityEntryTasks_236_);
v___x_243_ = v_reuseFailAlloc_248_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_st_ref_put(v___y_210_, v___x_243_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_240_);
v___x_246_ = v___x_217_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_240_);
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
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec(v_currNamespace_213_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_203_);
v_a_251_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_214_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_214_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec_ref(v___y_208_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_203_);
v_a_259_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_211_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_211_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
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
v___jp_267_:
{
lean_object* v_fileName_273_; lean_object* v_fileMap_274_; uint8_t v_suppressElabErrors_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_294_; 
v_fileName_273_ = lean_ctor_get(v___y_199_, 0);
v_fileMap_274_ = lean_ctor_get(v___y_199_, 1);
v_suppressElabErrors_275_ = lean_ctor_get_uint8(v___y_199_, sizeof(void*)*10);
v___x_276_ = lean_box(v_suppressElabErrors_275_);
v___x_277_ = lean_box(v___y_268_);
v___f_278_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_278_, 0, v___x_276_);
lean_closure_set(v___f_278_, 1, v___x_277_);
v___x_279_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_196_);
v___x_280_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v___x_279_, v___y_200_);
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_294_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_294_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_294_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_inc_ref_n(v_fileMap_274_, 2);
v___x_285_ = l_Lean_FileMap_toPosition(v_fileMap_274_, v___y_271_);
lean_dec(v___y_271_);
v___x_286_ = l_Lean_FileMap_toPosition(v_fileMap_274_, v___y_272_);
lean_dec(v___y_272_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0));
if (v_suppressElabErrors_275_ == 0)
{
lean_del_object(v___x_283_);
lean_dec_ref(v___f_278_);
v___y_203_ = v___x_285_;
v___y_204_ = v___y_269_;
v___y_205_ = v___x_287_;
v___y_206_ = v___y_270_;
v___y_207_ = v___x_288_;
v___y_208_ = v_a_281_;
v___y_209_ = v_fileName_273_;
v___y_210_ = v___y_200_;
goto v___jp_202_;
}
else
{
uint8_t v___x_289_; 
lean_inc(v_a_281_);
v___x_289_ = l_Lean_MessageData_hasTag(v___f_278_, v_a_281_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_292_; 
lean_dec_ref_known(v___x_287_, 1);
lean_dec_ref(v___x_285_);
lean_dec(v_a_281_);
v___x_290_ = lean_box(0);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_290_);
v___x_292_ = v___x_283_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
else
{
lean_del_object(v___x_283_);
v___y_203_ = v___x_285_;
v___y_204_ = v___y_269_;
v___y_205_ = v___x_287_;
v___y_206_ = v___y_270_;
v___y_207_ = v___x_288_;
v___y_208_ = v_a_281_;
v___y_209_ = v_fileName_273_;
v___y_210_ = v___y_200_;
goto v___jp_202_;
}
}
}
}
v___jp_295_:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Syntax_getTailPos_x3f(v___y_298_, v___y_297_);
lean_dec(v___y_298_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_inc(v___y_300_);
v___y_268_ = v___y_296_;
v___y_269_ = v___y_297_;
v___y_270_ = v___y_299_;
v___y_271_ = v___y_300_;
v___y_272_ = v___y_300_;
goto v___jp_267_;
}
else
{
lean_object* v_val_302_; 
v_val_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_val_302_);
lean_dec_ref_known(v___x_301_, 1);
v___y_268_ = v___y_296_;
v___y_269_ = v___y_297_;
v___y_270_ = v___y_299_;
v___y_271_ = v___y_300_;
v___y_272_ = v_val_302_;
goto v___jp_267_;
}
}
v___jp_303_:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Elab_Command_getRef___redArg(v___y_199_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v_ref_309_; lean_object* v___x_310_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref_known(v___x_307_, 1);
v_ref_309_ = l_Lean_replaceRef(v_ref_195_, v_a_308_);
lean_dec(v_a_308_);
v___x_310_ = l_Lean_Syntax_getPos_x3f(v_ref_309_, v___y_305_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v___x_311_; 
v___x_311_ = lean_unsigned_to_nat(0u);
v___y_296_ = v___y_304_;
v___y_297_ = v___y_305_;
v___y_298_ = v_ref_309_;
v___y_299_ = v___y_306_;
v___y_300_ = v___x_311_;
goto v___jp_295_;
}
else
{
lean_object* v_val_312_; 
v_val_312_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_val_312_);
lean_dec_ref_known(v___x_310_, 1);
v___y_296_ = v___y_304_;
v___y_297_ = v___y_305_;
v___y_298_ = v_ref_309_;
v___y_299_ = v___y_306_;
v___y_300_ = v_val_312_;
goto v___jp_295_;
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref(v_msgData_196_);
v_a_313_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_307_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_307_);
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
v___jp_322_:
{
if (v___y_325_ == 0)
{
v___y_304_ = v___y_323_;
v___y_305_ = v___y_324_;
v___y_306_ = v_severity_197_;
goto v___jp_303_;
}
else
{
v___y_304_ = v___y_323_;
v___y_305_ = v___y_324_;
v___y_306_ = v___x_321_;
goto v___jp_303_;
}
}
v___jp_326_:
{
if (v___y_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v_scopes_330_; lean_object* v___x_331_; lean_object* v_opts_332_; uint8_t v___x_333_; uint8_t v___x_334_; 
v___x_328_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_329_ = lean_st_ref_get(v___y_200_);
v_scopes_330_ = lean_ctor_get(v___x_329_, 2);
lean_inc(v_scopes_330_);
lean_dec(v___x_329_);
v___x_331_ = l_List_head_x21___redArg(v___x_328_, v_scopes_330_);
lean_dec(v_scopes_330_);
v_opts_332_ = lean_ctor_get(v___x_331_, 1);
lean_inc_ref(v_opts_332_);
lean_dec(v___x_331_);
v___x_333_ = 1;
v___x_334_ = l_Lean_instBEqMessageSeverity_beq(v_severity_197_, v___x_333_);
if (v___x_334_ == 0)
{
lean_dec_ref(v_opts_332_);
v___y_323_ = v___y_327_;
v___y_324_ = v___y_327_;
v___y_325_ = v___x_334_;
goto v___jp_322_;
}
else
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = l_Lean_warningAsError;
v___x_336_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(v_opts_332_, v___x_335_);
lean_dec_ref(v_opts_332_);
v___y_323_ = v___y_327_;
v___y_324_ = v___y_327_;
v___y_325_ = v___x_336_;
goto v___jp_322_;
}
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v_msgData_196_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_195_ = stack[0].m_obj;
lean_object* v_msgData_196_ = stack[1].m_obj;
uint8_t v_severity_197_ = stack[2].m_num;
uint8_t v_isSilent_198_ = stack[3].m_num;
lean_object* v___y_199_ = stack[4].m_obj;
lean_object* v___y_200_ = stack[5].m_obj;
lean_object* v_res_341_;
v_res_341_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(v_ref_195_, v_msgData_196_, v_severity_197_, v_isSilent_198_, v___y_199_, v___y_200_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_ref_342_, lean_object* v_msgData_343_, lean_object* v_severity_344_, lean_object* v_isSilent_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
uint8_t v_severity_boxed_349_; uint8_t v_isSilent_boxed_350_; lean_object* v_res_351_; 
v_severity_boxed_349_ = lean_unbox(v_severity_344_);
v_isSilent_boxed_350_ = lean_unbox(v_isSilent_345_);
v_res_351_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(v_ref_342_, v_msgData_343_, v_severity_boxed_349_, v_isSilent_boxed_350_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v_ref_342_);
return v_res_351_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(lean_object* v_ref_352_, lean_object* v_msgData_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
uint8_t v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; 
v___x_357_ = 1;
v___x_358_ = 0;
v___x_359_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(v_ref_352_, v_msgData_353_, v___x_357_, v___x_358_, v___y_354_, v___y_355_);
return v___x_359_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_352_ = stack[0].m_obj;
lean_object* v_msgData_353_ = stack[1].m_obj;
lean_object* v___y_354_ = stack[2].m_obj;
lean_object* v___y_355_ = stack[3].m_obj;
lean_object* v_res_360_;
v_res_360_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(v_ref_352_, v_msgData_353_, v___y_354_, v___y_355_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4___boxed(lean_object* v_ref_361_, lean_object* v_msgData_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(v_ref_361_, v_msgData_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v_ref_361_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__0));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__2));
v___x_372_ = l_Lean_stringToMessageData(v___x_371_);
return v___x_372_;
}
}
lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(lean_object* v_linterOption_373_, lean_object* v_stx_374_, lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_name_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_397_; 
v_name_379_ = lean_ctor_get(v_linterOption_373_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v_linterOption_373_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_linterOption_373_, 1);
lean_dec(v_unused_398_);
v___x_381_ = v_linterOption_373_;
v_isShared_382_ = v_isSharedCheck_397_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_name_379_);
lean_dec(v_linterOption_373_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_397_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_383_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1);
lean_inc(v_name_379_);
v___x_384_ = l_Lean_MessageData_ofName(v_name_379_);
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 7);
lean_ctor_set(v___x_381_, 1, v___x_384_);
lean_ctor_set(v___x_381_, 0, v___x_383_);
v___x_386_ = v___x_381_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_396_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v_disable_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_387_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v_disable_389_ = l_Lean_MessageData_note(v___x_388_);
v___x_390_ = l_Lean_Linter_linterMessageTag;
v___x_391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_391_, 0, v_msg_375_);
lean_ctor_set(v___x_391_, 1, v_disable_389_);
v___x_392_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_393_, 0, v_name_379_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
lean_inc(v_stx_374_);
v___x_394_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_394_, 0, v_stx_374_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(v_stx_374_, v___x_394_, v___y_376_, v___y_377_);
lean_dec(v_stx_374_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_373_ = stack[0].m_obj;
lean_object* v_stx_374_ = stack[1].m_obj;
lean_object* v_msg_375_ = stack[2].m_obj;
lean_object* v___y_376_ = stack[3].m_obj;
lean_object* v___y_377_ = stack[4].m_obj;
lean_object* v_res_399_;
v_res_399_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_373_, v_stx_374_, v_msg_375_, v___y_376_, v___y_377_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_400_, lean_object* v_stx_401_, lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_400_, v_stx_401_, v_msg_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_406_;
}
}
lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(lean_object* v_linterOption_407_, lean_object* v_stx_408_, lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_424_; 
v___x_413_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_410_, v___y_411_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_424_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_424_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_424_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
uint8_t v___x_418_; 
v___x_418_ = l_Lean_Linter_getLinterValue(v_linterOption_407_, v_a_414_);
lean_dec(v_a_414_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_421_; 
lean_dec_ref(v_msg_409_);
lean_dec(v_stx_408_);
lean_dec_ref(v_linterOption_407_);
v___x_419_ = lean_box(0);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_419_);
v___x_421_ = v___x_416_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
else
{
lean_object* v___x_423_; 
lean_del_object(v___x_416_);
v___x_423_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_407_, v_stx_408_, v_msg_409_, v___y_410_, v___y_411_);
return v___x_423_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_407_ = stack[0].m_obj;
lean_object* v_stx_408_ = stack[1].m_obj;
lean_object* v_msg_409_ = stack[2].m_obj;
lean_object* v___y_410_ = stack[3].m_obj;
lean_object* v___y_411_ = stack[4].m_obj;
lean_object* v_res_425_;
v_res_425_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(v_linterOption_407_, v_stx_408_, v_msg_409_, v___y_410_, v___y_411_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2___boxed(lean_object* v_linterOption_426_, lean_object* v_stx_427_, lean_object* v_msg_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(v_linterOption_426_, v_stx_427_, v_msg_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
return v_res_432_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(lean_object* v___x_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Meta_isProp(v___x_433_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
return v___x_441_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_433_ = stack[0].m_obj;
lean_object* v___y_434_ = stack[1].m_obj;
lean_object* v___y_435_ = stack[2].m_obj;
lean_object* v___y_436_ = stack[3].m_obj;
lean_object* v___y_437_ = stack[4].m_obj;
lean_object* v___y_438_ = stack[5].m_obj;
lean_object* v___y_439_ = stack[6].m_obj;
lean_object* v_res_442_;
v_res_442_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(v___x_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed(lean_object* v___x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(v___x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_451_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0));
v___x_454_ = l_Lean_stringToMessageData(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(lean_object* v___x_458_, uint8_t v___x_459_, lean_object* v_as_x27_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
if (lean_obj_tag(v_as_x27_460_) == 0)
{
lean_object* v___x_465_; 
lean_dec_ref(v___x_458_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v_b_461_);
return v___x_465_;
}
else
{
lean_object* v_head_466_; lean_object* v_tail_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_head_466_ = lean_ctor_get(v_as_x27_460_, 0);
v_tail_467_ = lean_ctor_get(v_as_x27_460_, 1);
v___x_468_ = lean_box(0);
lean_inc(v_head_466_);
lean_inc_ref(v___x_458_);
v___x_469_ = l_Lean_Environment_find_x3f(v___x_458_, v_head_466_, v___x_459_);
if (lean_obj_tag(v___x_469_) == 1)
{
lean_object* v_val_470_; uint8_t v___x_471_; 
v_val_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = l_Lean_ConstantInfo_isDefinition(v_val_470_);
if (v___x_471_ == 0)
{
lean_dec(v_val_470_);
v_as_x27_460_ = v_tail_467_;
v_b_461_ = v___x_468_;
goto _start;
}
else
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = l_Lean_ConstantInfo_hints(v_val_470_);
v___x_474_ = l_Lean_ReducibilityHints_isAbbrev(v___x_473_);
lean_dec(v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___f_477_; lean_object* v___x_478_; 
v___x_475_ = l_Lean_Linter_linter_defProp;
v___x_476_ = l_Lean_ConstantInfo_type(v_val_470_);
lean_dec(v_val_470_);
v___f_477_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_477_, 0, v___x_476_);
v___x_478_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_477_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; uint8_t v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v___x_480_ = lean_unbox(v_a_479_);
lean_dec(v_a_479_);
if (v___x_480_ == 0)
{
v_as_x27_460_ = v_tail_467_;
v_b_461_ = v___x_468_;
goto _start;
}
else
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Elab_Command_getRef___redArg(v___y_462_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1);
lean_inc(v_head_466_);
v___x_485_ = l_Lean_MessageData_ofConstName(v_head_466_, v___x_474_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(v___x_475_, v_a_483_, v___x_488_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_dec_ref_known(v___x_489_, 1);
v_as_x27_460_ = v_tail_467_;
v_b_461_ = v___x_468_;
goto _start;
}
else
{
lean_dec_ref(v___x_458_);
return v___x_489_;
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref(v___x_458_);
v_a_491_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_482_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_482_);
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
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec_ref(v___x_458_);
v_a_499_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_478_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_478_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
else
{
lean_dec(v_val_470_);
v_as_x27_460_ = v_tail_467_;
v_b_461_ = v___x_468_;
goto _start;
}
}
}
else
{
lean_dec(v___x_469_);
v_as_x27_460_ = v_tail_467_;
v_b_461_ = v___x_468_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_458_ = stack[0].m_obj;
uint8_t v___x_459_ = stack[1].m_num;
lean_object* v_as_x27_460_ = stack[2].m_obj;
lean_object* v_b_461_ = stack[3].m_obj;
lean_object* v___y_462_ = stack[4].m_obj;
lean_object* v___y_463_ = stack[5].m_obj;
lean_object* v_res_509_;
v_res_509_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_458_, v___x_459_, v_as_x27_460_, v_b_461_, v___y_462_, v___y_463_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___boxed(lean_object* v___x_510_, lean_object* v___x_511_, lean_object* v_as_x27_512_, lean_object* v_b_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
uint8_t v___x_9253__boxed_517_; lean_object* v_res_518_; 
v___x_9253__boxed_517_ = lean_unbox(v___x_511_);
v_res_518_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_510_, v___x_9253__boxed_517_, v_as_x27_512_, v_b_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v_as_x27_512_);
return v_res_518_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(lean_object* v___x_522_, uint8_t v___x_523_, lean_object* v_as_524_, size_t v_sz_525_, size_t v_i_526_, lean_object* v_b_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = lean_usize_dec_lt(v_i_526_, v_sz_525_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
lean_dec_ref(v___x_522_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v_b_527_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; lean_object* v_a_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec_ref(v_b_527_);
v___x_533_ = lean_box(0);
v_a_534_ = lean_array_uget_borrowed(v_as_524_, v_i_526_);
lean_inc(v_a_534_);
v___x_535_ = l_Lean_Linter_getDeclsByBody(v_a_534_);
lean_inc_ref(v___x_522_);
v___x_536_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_522_, v___x_523_, v___x_535_, v___x_533_, v___y_528_, v___y_529_);
lean_dec(v___x_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_537_; size_t v___x_538_; size_t v___x_539_; 
lean_dec_ref_known(v___x_536_, 1);
v___x_537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0));
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_add(v_i_526_, v___x_538_);
v_i_526_ = v___x_539_;
v_b_527_ = v___x_537_;
goto _start;
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v___x_522_);
v_a_541_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_536_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_536_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_522_ = stack[0].m_obj;
uint8_t v___x_523_ = stack[1].m_num;
lean_object* v_as_524_ = stack[2].m_obj;
size_t v_sz_525_ = stack[3].m_num;
size_t v_i_526_ = stack[4].m_num;
lean_object* v_b_527_ = stack[5].m_obj;
lean_object* v___y_528_ = stack[6].m_obj;
lean_object* v___y_529_ = stack[7].m_obj;
lean_object* v_res_549_;
v_res_549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_522_, v___x_523_, v_as_524_, v_sz_525_, v_i_526_, v_b_527_, v___y_528_, v___y_529_);
stack->m_obj
 = v_res_549_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___boxed(lean_object* v___x_550_, lean_object* v___x_551_, lean_object* v_as_552_, lean_object* v_sz_553_, lean_object* v_i_554_, lean_object* v_b_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___x_9430__boxed_559_; size_t v_sz_boxed_560_; size_t v_i_boxed_561_; lean_object* v_res_562_; 
v___x_9430__boxed_559_ = lean_unbox(v___x_551_);
v_sz_boxed_560_ = lean_unbox_usize(v_sz_553_);
lean_dec(v_sz_553_);
v_i_boxed_561_ = lean_unbox_usize(v_i_554_);
lean_dec(v_i_554_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_550_, v___x_9430__boxed_559_, v_as_552_, v_sz_boxed_560_, v_i_boxed_561_, v_b_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec_ref(v_as_552_);
return v_res_562_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(lean_object* v___x_563_, uint8_t v___x_564_, lean_object* v_as_565_, size_t v_sz_566_, size_t v_i_567_, lean_object* v_b_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
uint8_t v___x_572_; 
v___x_572_ = lean_usize_dec_lt(v_i_567_, v_sz_566_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_dec_ref(v___x_563_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v_b_568_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref(v_b_568_);
v___x_574_ = lean_box(0);
v_a_575_ = lean_array_uget_borrowed(v_as_565_, v_i_567_);
lean_inc(v_a_575_);
v___x_576_ = l_Lean_Linter_getDeclsByBody(v_a_575_);
lean_inc_ref(v___x_563_);
v___x_577_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_563_, v___x_564_, v___x_576_, v___x_574_, v___y_569_, v___y_570_);
lean_dec(v___x_576_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v___x_578_; size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; 
lean_dec_ref_known(v___x_577_, 1);
v___x_578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0));
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_add(v_i_567_, v___x_579_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_563_, v___x_564_, v_as_565_, v_sz_566_, v___x_580_, v___x_578_, v___y_569_, v___y_570_);
return v___x_581_;
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v___x_563_);
v_a_582_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_577_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_577_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_563_ = stack[0].m_obj;
uint8_t v___x_564_ = stack[1].m_num;
lean_object* v_as_565_ = stack[2].m_obj;
size_t v_sz_566_ = stack[3].m_num;
size_t v_i_567_ = stack[4].m_num;
lean_object* v_b_568_ = stack[5].m_obj;
lean_object* v___y_569_ = stack[6].m_obj;
lean_object* v___y_570_ = stack[7].m_obj;
lean_object* v_res_590_;
v_res_590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_563_, v___x_564_, v_as_565_, v_sz_566_, v_i_567_, v_b_568_, v___y_569_, v___y_570_);
stack->m_obj
 = v_res_590_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9___boxed(lean_object* v___x_591_, lean_object* v___x_592_, lean_object* v_as_593_, lean_object* v_sz_594_, lean_object* v_i_595_, lean_object* v_b_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
uint8_t v___x_9516__boxed_600_; size_t v_sz_boxed_601_; size_t v_i_boxed_602_; lean_object* v_res_603_; 
v___x_9516__boxed_600_ = lean_unbox(v___x_592_);
v_sz_boxed_601_ = lean_unbox_usize(v_sz_594_);
lean_dec(v_sz_594_);
v_i_boxed_602_ = lean_unbox_usize(v_i_595_);
lean_dec(v_i_595_);
v_res_603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_591_, v___x_9516__boxed_600_, v_as_593_, v_sz_boxed_601_, v_i_boxed_602_, v_b_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v_as_593_);
return v_res_603_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(lean_object* v_init_604_, lean_object* v___x_605_, uint8_t v___x_606_, lean_object* v_n_607_, lean_object* v_b_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
if (lean_obj_tag(v_n_607_) == 0)
{
lean_object* v_cs_612_; lean_object* v___x_613_; lean_object* v___x_614_; size_t v_sz_615_; size_t v___x_616_; lean_object* v___x_617_; 
v_cs_612_ = lean_ctor_get(v_n_607_, 0);
v___x_613_ = lean_box(0);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v_b_608_);
v_sz_615_ = lean_array_size(v_cs_612_);
v___x_616_ = ((size_t)0ULL);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_604_, v___x_605_, v___x_606_, v_cs_612_, v_sz_615_, v___x_616_, v___x_614_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_632_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_632_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_fst_622_; 
v_fst_622_ = lean_ctor_get(v_a_618_, 0);
if (lean_obj_tag(v_fst_622_) == 0)
{
lean_object* v_snd_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v_snd_623_ = lean_ctor_get(v_a_618_, 1);
lean_inc(v_snd_623_);
lean_dec(v_a_618_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v_snd_623_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_626_ = v___x_620_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v_val_628_; lean_object* v___x_630_; 
lean_inc_ref(v_fst_622_);
lean_dec(v_a_618_);
v_val_628_ = lean_ctor_get(v_fst_622_, 0);
lean_inc(v_val_628_);
lean_dec_ref_known(v_fst_622_, 1);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_val_628_);
v___x_630_ = v___x_620_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_val_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_a_633_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_617_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_617_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
else
{
lean_object* v_vs_641_; lean_object* v___x_642_; lean_object* v___x_643_; size_t v_sz_644_; size_t v___x_645_; lean_object* v___x_646_; 
v_vs_641_ = lean_ctor_get(v_n_607_, 0);
v___x_642_ = lean_box(0);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v_b_608_);
v_sz_644_ = lean_array_size(v_vs_641_);
v___x_645_ = ((size_t)0ULL);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_605_, v___x_606_, v_vs_641_, v_sz_644_, v___x_645_, v___x_643_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_661_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_661_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_661_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_661_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_fst_651_; 
v_fst_651_ = lean_ctor_get(v_a_647_, 0);
if (lean_obj_tag(v_fst_651_) == 0)
{
lean_object* v_snd_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v_snd_652_ = lean_ctor_get(v_a_647_, 1);
lean_inc(v_snd_652_);
lean_dec(v_a_647_);
v___x_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_653_, 0, v_snd_652_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_653_);
v___x_655_ = v___x_649_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
else
{
lean_object* v_val_657_; lean_object* v___x_659_; 
lean_inc_ref(v_fst_651_);
lean_dec(v_a_647_);
v_val_657_ = lean_ctor_get(v_fst_651_, 0);
lean_inc(v_val_657_);
lean_dec_ref_known(v_fst_651_, 1);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v_val_657_);
v___x_659_ = v___x_649_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_val_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_646_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_646_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_604_ = stack[0].m_obj;
lean_object* v___x_605_ = stack[1].m_obj;
uint8_t v___x_606_ = stack[2].m_num;
lean_object* v_n_607_ = stack[3].m_obj;
lean_object* v_b_608_ = stack[4].m_obj;
lean_object* v___y_609_ = stack[5].m_obj;
lean_object* v___y_610_ = stack[6].m_obj;
lean_object* v_res_670_;
v_res_670_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_604_, v___x_605_, v___x_606_, v_n_607_, v_b_608_, v___y_609_, v___y_610_);
stack->m_obj
 = v_res_670_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(lean_object* v_init_671_, lean_object* v___x_672_, uint8_t v___x_673_, lean_object* v_as_674_, size_t v_sz_675_, size_t v_i_676_, lean_object* v_b_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
uint8_t v___x_681_; 
v___x_681_ = lean_usize_dec_lt(v_i_676_, v_sz_675_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec_ref(v___x_672_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v_b_677_);
return v___x_682_;
}
else
{
lean_object* v_snd_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_717_; 
v_snd_683_ = lean_ctor_get(v_b_677_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_b_677_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; 
v_unused_718_ = lean_ctor_get(v_b_677_, 0);
lean_dec(v_unused_718_);
v___x_685_ = v_b_677_;
v_isShared_686_ = v_isSharedCheck_717_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snd_683_);
lean_dec(v_b_677_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_717_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v_a_688_; lean_object* v___x_689_; 
v___x_687_ = lean_box(0);
v_a_688_ = lean_array_uget_borrowed(v_as_674_, v_i_676_);
lean_inc(v_snd_683_);
lean_inc_ref(v___x_672_);
v___x_689_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_671_, v___x_672_, v___x_673_, v_a_688_, v_snd_683_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_708_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_708_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_708_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_708_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
if (lean_obj_tag(v_a_690_) == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_dec_ref(v___x_672_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v_a_690_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_694_);
v___x_696_ = v___x_685_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_snd_683_);
v___x_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_696_);
v___x_698_ = v___x_692_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; 
lean_del_object(v___x_692_);
lean_dec(v_snd_683_);
v_a_701_ = lean_ctor_get(v_a_690_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v_a_690_, 1);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_a_701_);
lean_ctor_set(v___x_685_, 0, v___x_687_);
v___x_703_ = v___x_685_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_a_701_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
size_t v___x_704_; size_t v___x_705_; 
v___x_704_ = ((size_t)1ULL);
v___x_705_ = lean_usize_add(v_i_676_, v___x_704_);
v_i_676_ = v___x_705_;
v_b_677_ = v___x_703_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_del_object(v___x_685_);
lean_dec(v_snd_683_);
lean_dec_ref(v___x_672_);
v_a_709_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_689_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_689_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_671_ = stack[0].m_obj;
lean_object* v___x_672_ = stack[1].m_obj;
uint8_t v___x_673_ = stack[2].m_num;
lean_object* v_as_674_ = stack[3].m_obj;
size_t v_sz_675_ = stack[4].m_num;
size_t v_i_676_ = stack[5].m_num;
lean_object* v_b_677_ = stack[6].m_obj;
lean_object* v___y_678_ = stack[7].m_obj;
lean_object* v___y_679_ = stack[8].m_obj;
lean_object* v_res_719_;
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_671_, v___x_672_, v___x_673_, v_as_674_, v_sz_675_, v_i_676_, v_b_677_, v___y_678_, v___y_679_);
stack->m_obj
 = v_res_719_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8___boxed(lean_object* v_init_720_, lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v_as_723_, lean_object* v_sz_724_, lean_object* v_i_725_, lean_object* v_b_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v___x_9594__boxed_730_; size_t v_sz_boxed_731_; size_t v_i_boxed_732_; lean_object* v_res_733_; 
v___x_9594__boxed_730_ = lean_unbox(v___x_722_);
v_sz_boxed_731_ = lean_unbox_usize(v_sz_724_);
lean_dec(v_sz_724_);
v_i_boxed_732_ = lean_unbox_usize(v_i_725_);
lean_dec(v_i_725_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_720_, v___x_721_, v___x_9594__boxed_730_, v_as_723_, v_sz_boxed_731_, v_i_boxed_732_, v_b_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec_ref(v_as_723_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6___boxed(lean_object* v_init_734_, lean_object* v___x_735_, lean_object* v___x_736_, lean_object* v_n_737_, lean_object* v_b_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
uint8_t v___x_9615__boxed_742_; lean_object* v_res_743_; 
v___x_9615__boxed_742_ = lean_unbox(v___x_736_);
v_res_743_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_734_, v___x_735_, v___x_9615__boxed_742_, v_n_737_, v_b_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec_ref(v_n_737_);
return v_res_743_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(lean_object* v___x_747_, uint8_t v___x_748_, lean_object* v_as_749_, size_t v_sz_750_, size_t v_i_751_, lean_object* v_b_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = lean_usize_dec_lt(v_i_751_, v_sz_750_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec_ref(v___x_747_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v_b_752_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec_ref(v_b_752_);
v___x_758_ = lean_box(0);
v_a_759_ = lean_array_uget_borrowed(v_as_749_, v_i_751_);
lean_inc(v_a_759_);
v___x_760_ = l_Lean_Linter_getDeclsByBody(v_a_759_);
lean_inc_ref(v___x_747_);
v___x_761_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_747_, v___x_748_, v___x_760_, v___x_758_, v___y_753_, v___y_754_);
lean_dec(v___x_760_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v___x_762_; size_t v___x_763_; size_t v___x_764_; 
lean_dec_ref_known(v___x_761_, 1);
v___x_762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0));
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_751_, v___x_763_);
v_i_751_ = v___x_764_;
v_b_752_ = v___x_762_;
goto _start;
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v___x_747_);
v_a_766_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_761_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_761_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_747_ = stack[0].m_obj;
uint8_t v___x_748_ = stack[1].m_num;
lean_object* v_as_749_ = stack[2].m_obj;
size_t v_sz_750_ = stack[3].m_num;
size_t v_i_751_ = stack[4].m_num;
lean_object* v_b_752_ = stack[5].m_obj;
lean_object* v___y_753_ = stack[6].m_obj;
lean_object* v___y_754_ = stack[7].m_obj;
lean_object* v_res_774_;
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_747_, v___x_748_, v_as_749_, v_sz_750_, v_i_751_, v_b_752_, v___y_753_, v___y_754_);
stack->m_obj
 = v_res_774_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___boxed(lean_object* v___x_775_, lean_object* v___x_776_, lean_object* v_as_777_, lean_object* v_sz_778_, lean_object* v_i_779_, lean_object* v_b_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
uint8_t v___x_9915__boxed_784_; size_t v_sz_boxed_785_; size_t v_i_boxed_786_; lean_object* v_res_787_; 
v___x_9915__boxed_784_ = lean_unbox(v___x_776_);
v_sz_boxed_785_ = lean_unbox_usize(v_sz_778_);
lean_dec(v_sz_778_);
v_i_boxed_786_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_res_787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_775_, v___x_9915__boxed_784_, v_as_777_, v_sz_boxed_785_, v_i_boxed_786_, v_b_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v_as_777_);
return v_res_787_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(lean_object* v___x_788_, uint8_t v___x_789_, lean_object* v_as_790_, size_t v_sz_791_, size_t v_i_792_, lean_object* v_b_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_lt(v_i_792_, v_sz_791_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec_ref(v___x_788_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v_b_793_);
return v___x_798_;
}
else
{
lean_object* v___x_799_; lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref(v_b_793_);
v___x_799_ = lean_box(0);
v_a_800_ = lean_array_uget_borrowed(v_as_790_, v_i_792_);
lean_inc(v_a_800_);
v___x_801_ = l_Lean_Linter_getDeclsByBody(v_a_800_);
lean_inc_ref(v___x_788_);
v___x_802_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_788_, v___x_789_, v___x_801_, v___x_799_, v___y_794_, v___y_795_);
lean_dec(v___x_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
lean_dec_ref_known(v___x_802_, 1);
v___x_803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0));
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_add(v_i_792_, v___x_804_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_788_, v___x_789_, v_as_790_, v_sz_791_, v___x_805_, v___x_803_, v___y_794_, v___y_795_);
return v___x_806_;
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v___x_788_);
v_a_807_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_802_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_802_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_788_ = stack[0].m_obj;
uint8_t v___x_789_ = stack[1].m_num;
lean_object* v_as_790_ = stack[2].m_obj;
size_t v_sz_791_ = stack[3].m_num;
size_t v_i_792_ = stack[4].m_num;
lean_object* v_b_793_ = stack[5].m_obj;
lean_object* v___y_794_ = stack[6].m_obj;
lean_object* v___y_795_ = stack[7].m_obj;
lean_object* v_res_815_;
v_res_815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_788_, v___x_789_, v_as_790_, v_sz_791_, v_i_792_, v_b_793_, v___y_794_, v___y_795_);
stack->m_obj
 = v_res_815_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7___boxed(lean_object* v___x_816_, lean_object* v___x_817_, lean_object* v_as_818_, lean_object* v_sz_819_, lean_object* v_i_820_, lean_object* v_b_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
uint8_t v___x_10001__boxed_825_; size_t v_sz_boxed_826_; size_t v_i_boxed_827_; lean_object* v_res_828_; 
v___x_10001__boxed_825_ = lean_unbox(v___x_817_);
v_sz_boxed_826_ = lean_unbox_usize(v_sz_819_);
lean_dec(v_sz_819_);
v_i_boxed_827_ = lean_unbox_usize(v_i_820_);
lean_dec(v_i_820_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_816_, v___x_10001__boxed_825_, v_as_818_, v_sz_boxed_826_, v_i_boxed_827_, v_b_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec_ref(v_as_818_);
return v_res_828_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(lean_object* v___x_829_, uint8_t v___x_830_, lean_object* v_t_831_, lean_object* v_init_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_root_836_; lean_object* v_tail_837_; lean_object* v___x_838_; 
v_root_836_ = lean_ctor_get(v_t_831_, 0);
v_tail_837_ = lean_ctor_get(v_t_831_, 1);
lean_inc_ref(v___x_829_);
v___x_838_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_832_, v___x_829_, v___x_830_, v_root_836_, v_init_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_875_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_875_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_875_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_875_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
if (lean_obj_tag(v_a_839_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; 
lean_dec_ref(v___x_829_);
v_a_843_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v_a_839_, 1);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v_a_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_848_; lean_object* v___x_849_; size_t v_sz_850_; size_t v___x_851_; lean_object* v___x_852_; 
lean_del_object(v___x_841_);
v_a_847_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v_a_839_, 1);
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v_a_847_);
v_sz_850_ = lean_array_size(v_tail_837_);
v___x_851_ = ((size_t)0ULL);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_829_, v___x_830_, v_tail_837_, v_sz_850_, v___x_851_, v___x_849_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_866_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_866_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_866_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_866_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_fst_857_; 
v_fst_857_ = lean_ctor_get(v_a_853_, 0);
if (lean_obj_tag(v_fst_857_) == 0)
{
lean_object* v_snd_858_; lean_object* v___x_860_; 
v_snd_858_ = lean_ctor_get(v_a_853_, 1);
lean_inc(v_snd_858_);
lean_dec(v_a_853_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_snd_858_);
v___x_860_ = v___x_855_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_snd_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
else
{
lean_object* v_val_862_; lean_object* v___x_864_; 
lean_inc_ref(v_fst_857_);
lean_dec(v_a_853_);
v_val_862_ = lean_ctor_get(v_fst_857_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_fst_857_, 1);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_val_862_);
v___x_864_ = v___x_855_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_val_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_a_867_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_852_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_852_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v___x_829_);
v_a_876_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_838_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_838_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_829_ = stack[0].m_obj;
uint8_t v___x_830_ = stack[1].m_num;
lean_object* v_t_831_ = stack[2].m_obj;
lean_object* v_init_832_ = stack[3].m_obj;
lean_object* v___y_833_ = stack[4].m_obj;
lean_object* v___y_834_ = stack[5].m_obj;
lean_object* v_res_884_;
v_res_884_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(v___x_829_, v___x_830_, v_t_831_, v_init_832_, v___y_833_, v___y_834_);
stack->m_obj
 = v_res_884_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4___boxed(lean_object* v___x_885_, lean_object* v___x_886_, lean_object* v_t_887_, lean_object* v_init_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v___x_10079__boxed_892_; lean_object* v_res_893_; 
v___x_10079__boxed_892_ = lean_unbox(v___x_886_);
v_res_893_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(v___x_885_, v___x_10079__boxed_892_, v_t_887_, v_init_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec_ref(v_t_887_);
return v_res_893_;
}
}
lean_object* l_Lean_Linter_DefProp_defPropLinter___lam__0(lean_object* v_x_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_930_; 
v___x_898_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_895_, v___y_896_);
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_930_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_930_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_930_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = l_Lean_Linter_linter_defProp;
v___x_904_ = l_Lean_Linter_getLinterValue(v___x_903_, v_a_899_);
lean_dec(v_a_899_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_box(0);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_905_);
v___x_907_ = v___x_901_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
else
{
lean_object* v___x_909_; lean_object* v_messages_910_; uint8_t v___x_911_; 
v___x_909_ = lean_st_ref_get(v___y_896_);
v_messages_910_ = lean_ctor_get(v___x_909_, 1);
lean_inc_ref(v_messages_910_);
lean_dec(v___x_909_);
v___x_911_ = l_Lean_MessageLog_hasErrors(v_messages_910_);
lean_dec_ref(v_messages_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v_env_913_; lean_object* v___x_914_; lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_del_object(v___x_901_);
v___x_912_ = lean_st_ref_get(v___y_896_);
v_env_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_env_913_);
lean_dec(v___x_912_);
v___x_914_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(v___y_896_);
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref(v___x_914_);
v___x_916_ = lean_box(0);
v___x_917_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(v_env_913_, v___x_911_, v_a_915_, v___x_916_, v___y_895_, v___y_896_);
lean_dec(v_a_915_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v___x_917_, 0);
lean_dec(v_unused_925_);
v___x_919_ = v___x_917_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_dec(v___x_917_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_916_);
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_916_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
else
{
return v___x_917_;
}
}
else
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_box(0);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_926_);
v___x_928_ = v___x_901_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_DefProp_defPropLinter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_894_ = stack[0].m_obj;
lean_object* v___y_895_ = stack[1].m_obj;
lean_object* v___y_896_ = stack[2].m_obj;
lean_object* v_res_931_;
v_res_931_ = l_Lean_Linter_DefProp_defPropLinter___lam__0(v_x_894_, v___y_895_, v___y_896_);
stack->m_obj
 = v_res_931_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_DefProp_defPropLinter___lam__0___boxed(lean_object* v_x_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Linter_DefProp_defPropLinter___lam__0(v_x_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v_x_932_);
return v_res_936_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(lean_object* v_o_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_o_951_, v___y_953_);
return v___x_955_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_951_ = stack[0].m_obj;
lean_object* v___y_952_ = stack[1].m_obj;
lean_object* v___y_953_ = stack[2].m_obj;
lean_object* v_res_956_;
v_res_956_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(v_o_951_, v___y_952_, v___y_953_);
stack->m_obj
 = v_res_956_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___boxed(lean_object* v_o_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(v_o_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
return v_res_961_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(lean_object* v___x_962_, uint8_t v___x_963_, lean_object* v_as_964_, lean_object* v_as_x27_965_, lean_object* v_b_966_, lean_object* v_a_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_962_, v___x_963_, v_as_x27_965_, v_b_966_, v___y_968_, v___y_969_);
return v___x_971_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_962_ = stack[0].m_obj;
uint8_t v___x_963_ = stack[1].m_num;
lean_object* v_as_964_ = stack[2].m_obj;
lean_object* v_as_x27_965_ = stack[3].m_obj;
lean_object* v_b_966_ = stack[4].m_obj;
lean_object* v___y_968_ = stack[6].m_obj;
lean_object* v___y_969_ = stack[7].m_obj;
lean_object* v_res_972_;
v_res_972_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(v___x_962_, v___x_963_, v_as_964_, v_as_x27_965_, v_b_966_, lean_box(0), v___y_968_, v___y_969_);
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___boxed(lean_object* v___x_973_, lean_object* v___x_974_, lean_object* v_as_975_, lean_object* v_as_x27_976_, lean_object* v_b_977_, lean_object* v_a_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v___x_10425__boxed_982_; lean_object* v_res_983_; 
v___x_10425__boxed_982_ = lean_unbox(v___x_974_);
v_res_983_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(v___x_973_, v___x_10425__boxed_982_, v_as_975_, v_as_x27_976_, v_b_977_, v_a_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v_as_x27_976_);
lean_dec(v_as_975_);
return v_res_983_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_msgData_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_msgData_984_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_984_ = stack[0].m_obj;
lean_object* v___y_985_ = stack[1].m_obj;
lean_object* v___y_986_ = stack[2].m_obj;
lean_object* v_res_989_;
v_res_989_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(v_msgData_984_, v___y_985_, v___y_986_);
stack->m_obj
 = v_res_989_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_msgData_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(v_msgData_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_994_;
}
}
lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_Linter_DefProp_defPropLinter));
v___x_997_ = l_Lean_Elab_Command_addLinter(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_998_;
v_res_998_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_();
stack->m_obj
 = v_res_998_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2____boxed(lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_();
return v_res_1000_;
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
