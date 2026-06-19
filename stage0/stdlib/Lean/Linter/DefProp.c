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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Linter_DefProp_defPropLinter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__0_value)} };
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
lean_object* v___x_79_; lean_object* v_env_80_; lean_object* v___x_81_; lean_object* v_toEnvExtension_82_; lean_object* v_asyncMode_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_merged_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
v___x_79_ = lean_st_ref_get(v___y_77_);
v_env_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc_ref(v_env_80_);
lean_dec(v___x_79_);
v___x_81_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_82_ = lean_ctor_get(v___x_81_, 0);
v_asyncMode_83_ = lean_ctor_get(v_toEnvExtension_82_, 2);
v___x_84_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_85_ = lean_box(0);
v___x_86_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_84_, v___x_81_, v_env_80_, v_asyncMode_83_, v___x_85_);
v_merged_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; 
v_unused_96_ = lean_ctor_get(v___x_86_, 1);
lean_dec(v_unused_96_);
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_merged_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_merged_87_);
lean_ctor_set(v___x_89_, 0, v_o_76_);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_o_76_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_merged_87_);
v___x_92_ = v_reuseFailAlloc_94_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg___boxed(lean_object* v_o_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_o_97_, v___y_98_);
lean_dec(v___y_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; lean_object* v_scopes_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_opts_108_; lean_object* v___x_109_; 
v___x_104_ = lean_st_ref_get(v___y_102_);
v_scopes_105_ = lean_ctor_get(v___x_104_, 2);
lean_inc(v_scopes_105_);
lean_dec(v___x_104_);
v___x_106_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_107_ = l_List_head_x21___redArg(v___x_106_, v_scopes_105_);
lean_dec(v_scopes_105_);
v_opts_108_ = lean_ctor_get(v___x_107_, 1);
lean_inc_ref(v_opts_108_);
lean_dec(v___x_107_);
v___x_109_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_opts_108_, v___y_102_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0___boxed(lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_113_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(uint8_t v___y_115_, uint8_t v_suppressElabErrors_116_, lean_object* v_x_117_){
_start:
{
if (lean_obj_tag(v_x_117_) == 1)
{
lean_object* v_pre_118_; 
v_pre_118_ = lean_ctor_get(v_x_117_, 0);
if (lean_obj_tag(v_pre_118_) == 0)
{
lean_object* v_str_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v_str_119_ = lean_ctor_get(v_x_117_, 1);
v___x_120_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___closed__0));
v___x_121_ = lean_string_dec_eq(v_str_119_, v___x_120_);
if (v___x_121_ == 0)
{
return v___y_115_;
}
else
{
return v_suppressElabErrors_116_;
}
}
else
{
return v___y_115_;
}
}
else
{
return v___y_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed(lean_object* v___y_122_, lean_object* v_suppressElabErrors_123_, lean_object* v_x_124_){
_start:
{
uint8_t v___y_9515__boxed_125_; uint8_t v_suppressElabErrors_boxed_126_; uint8_t v_res_127_; lean_object* v_r_128_; 
v___y_9515__boxed_125_ = lean_unbox(v___y_122_);
v_suppressElabErrors_boxed_126_ = lean_unbox(v_suppressElabErrors_123_);
v_res_127_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(v___y_9515__boxed_125_, v_suppressElabErrors_boxed_126_, v_x_124_);
lean_dec(v_x_124_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_129_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__0);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
lean_ctor_set(v___x_134_, 3, v___x_133_);
lean_ctor_set(v___x_134_, 4, v___x_132_);
lean_ctor_set(v___x_134_, 5, v___x_132_);
lean_ctor_set(v___x_134_, 6, v___x_132_);
lean_ctor_set(v___x_134_, 7, v___x_132_);
lean_ctor_set(v___x_134_, 8, v___x_132_);
lean_ctor_set(v___x_134_, 9, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_unsigned_to_nat(32u);
v___x_136_ = lean_mk_empty_array_with_capacity(v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_138_ = ((size_t)5ULL);
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_unsigned_to_nat(32u);
v___x_141_ = lean_mk_empty_array_with_capacity(v___x_140_);
v___x_142_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__3);
v___x_143_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v___x_139_);
lean_ctor_set(v___x_143_, 3, v___x_139_);
lean_ctor_set_usize(v___x_143_, 4, v___x_138_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = lean_box(1);
v___x_145_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__4);
v___x_146_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__1);
v___x_147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_145_);
lean_ctor_set(v___x_147_, 2, v___x_144_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_msgData_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; lean_object* v_env_152_; lean_object* v___x_153_; lean_object* v_scopes_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_opts_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_151_ = lean_st_ref_get(v___y_149_);
v_env_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_ref(v_env_152_);
lean_dec(v___x_151_);
v___x_153_ = lean_st_ref_get(v___y_149_);
v_scopes_154_ = lean_ctor_get(v___x_153_, 2);
lean_inc(v_scopes_154_);
lean_dec(v___x_153_);
v___x_155_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_156_ = l_List_head_x21___redArg(v___x_155_, v_scopes_154_);
lean_dec(v_scopes_154_);
v_opts_157_ = lean_ctor_get(v___x_156_, 1);
lean_inc_ref(v_opts_157_);
lean_dec(v___x_156_);
v___x_158_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__2);
v___x_159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___closed__5);
v___x_160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_160_, 0, v_env_152_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v___x_159_);
lean_ctor_set(v___x_160_, 3, v_opts_157_);
v___x_161_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v_msgData_148_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_msgData_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_msgData_163_, v___y_164_);
lean_dec(v___y_164_);
return v_res_166_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(lean_object* v_opts_167_, lean_object* v_opt_168_){
_start:
{
lean_object* v_name_169_; lean_object* v_defValue_170_; lean_object* v_map_171_; lean_object* v___x_172_; 
v_name_169_ = lean_ctor_get(v_opt_168_, 0);
v_defValue_170_ = lean_ctor_get(v_opt_168_, 1);
v_map_171_ = lean_ctor_get(v_opts_167_, 0);
v___x_172_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_171_, v_name_169_);
if (lean_obj_tag(v___x_172_) == 0)
{
uint8_t v___x_173_; 
v___x_173_ = lean_unbox(v_defValue_170_);
return v___x_173_;
}
else
{
lean_object* v_val_174_; 
v_val_174_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_val_174_);
lean_dec_ref_known(v___x_172_, 1);
if (lean_obj_tag(v_val_174_) == 1)
{
uint8_t v_v_175_; 
v_v_175_ = lean_ctor_get_uint8(v_val_174_, 0);
lean_dec_ref_known(v_val_174_, 0);
return v_v_175_;
}
else
{
uint8_t v___x_176_; 
lean_dec(v_val_174_);
v___x_176_ = lean_unbox(v_defValue_170_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_opts_177_, lean_object* v_opt_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(v_opts_177_, v_opt_178_);
lean_dec_ref(v_opt_178_);
lean_dec_ref(v_opts_177_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(lean_object* v_ref_182_, lean_object* v_msgData_183_, uint8_t v_severity_184_, uint8_t v_isSilent_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___y_190_; uint8_t v___y_191_; lean_object* v___y_192_; uint8_t v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; uint8_t v___y_253_; lean_object* v___y_254_; uint8_t v___y_255_; uint8_t v___y_256_; lean_object* v___y_257_; uint8_t v___y_281_; uint8_t v___y_282_; uint8_t v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; uint8_t v___y_289_; uint8_t v___y_290_; uint8_t v___y_291_; uint8_t v___x_306_; uint8_t v___y_308_; uint8_t v___y_309_; uint8_t v___y_310_; uint8_t v___y_312_; uint8_t v___x_324_; 
v___x_306_ = 2;
v___x_324_ = l_Lean_instBEqMessageSeverity_beq(v_severity_184_, v___x_306_);
if (v___x_324_ == 0)
{
v___y_312_ = v___x_324_;
goto v___jp_311_;
}
else
{
uint8_t v___x_325_; 
lean_inc_ref(v_msgData_183_);
v___x_325_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_183_);
v___y_312_ = v___x_325_;
goto v___jp_311_;
}
v___jp_189_:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Elab_Command_getScope___redArg(v___y_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
v___x_200_ = l_Lean_Elab_Command_getScope___redArg(v___y_197_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_235_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_235_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_235_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_235_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v_currNamespace_206_; lean_object* v_openDecls_207_; lean_object* v_env_208_; lean_object* v_messages_209_; lean_object* v_scopes_210_; lean_object* v_usedQuotCtxts_211_; lean_object* v_nextMacroScope_212_; lean_object* v_maxRecDepth_213_; lean_object* v_ngen_214_; lean_object* v_auxDeclNGen_215_; lean_object* v_infoState_216_; lean_object* v_traceState_217_; lean_object* v_snapshotTasks_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_234_; 
v___x_205_ = lean_st_ref_take(v___y_197_);
v_currNamespace_206_ = lean_ctor_get(v_a_199_, 2);
lean_inc(v_currNamespace_206_);
lean_dec(v_a_199_);
v_openDecls_207_ = lean_ctor_get(v_a_201_, 3);
lean_inc(v_openDecls_207_);
lean_dec(v_a_201_);
v_env_208_ = lean_ctor_get(v___x_205_, 0);
v_messages_209_ = lean_ctor_get(v___x_205_, 1);
v_scopes_210_ = lean_ctor_get(v___x_205_, 2);
v_usedQuotCtxts_211_ = lean_ctor_get(v___x_205_, 3);
v_nextMacroScope_212_ = lean_ctor_get(v___x_205_, 4);
v_maxRecDepth_213_ = lean_ctor_get(v___x_205_, 5);
v_ngen_214_ = lean_ctor_get(v___x_205_, 6);
v_auxDeclNGen_215_ = lean_ctor_get(v___x_205_, 7);
v_infoState_216_ = lean_ctor_get(v___x_205_, 8);
v_traceState_217_ = lean_ctor_get(v___x_205_, 9);
v_snapshotTasks_218_ = lean_ctor_get(v___x_205_, 10);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_234_ == 0)
{
v___x_220_ = v___x_205_;
v_isShared_221_ = v_isSharedCheck_234_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_snapshotTasks_218_);
lean_inc(v_traceState_217_);
lean_inc(v_infoState_216_);
lean_inc(v_auxDeclNGen_215_);
lean_inc(v_ngen_214_);
lean_inc(v_maxRecDepth_213_);
lean_inc(v_nextMacroScope_212_);
lean_inc(v_usedQuotCtxts_211_);
lean_inc(v_scopes_210_);
lean_inc(v_messages_209_);
lean_inc(v_env_208_);
lean_dec(v___x_205_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_234_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_currNamespace_206_);
lean_ctor_set(v___x_222_, 1, v_openDecls_207_);
v___x_223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___y_194_);
lean_inc_ref(v___y_190_);
lean_inc_ref(v___y_195_);
v___x_224_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_224_, 0, v___y_195_);
lean_ctor_set(v___x_224_, 1, v___y_196_);
lean_ctor_set(v___x_224_, 2, v___y_192_);
lean_ctor_set(v___x_224_, 3, v___y_190_);
lean_ctor_set(v___x_224_, 4, v___x_223_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*5, v___y_193_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*5 + 1, v___y_191_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*5 + 2, v_isSilent_185_);
v___x_225_ = l_Lean_MessageLog_add(v___x_224_, v_messages_209_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 1, v___x_225_);
v___x_227_ = v___x_220_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_env_208_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_scopes_210_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v_usedQuotCtxts_211_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v_nextMacroScope_212_);
lean_ctor_set(v_reuseFailAlloc_233_, 5, v_maxRecDepth_213_);
lean_ctor_set(v_reuseFailAlloc_233_, 6, v_ngen_214_);
lean_ctor_set(v_reuseFailAlloc_233_, 7, v_auxDeclNGen_215_);
lean_ctor_set(v_reuseFailAlloc_233_, 8, v_infoState_216_);
lean_ctor_set(v_reuseFailAlloc_233_, 9, v_traceState_217_);
lean_ctor_set(v_reuseFailAlloc_233_, 10, v_snapshotTasks_218_);
v___x_227_ = v_reuseFailAlloc_233_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_228_ = lean_st_ref_set(v___y_197_, v___x_227_);
v___x_229_ = lean_box(0);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_229_);
v___x_231_ = v___x_203_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_a_199_);
lean_dec_ref(v___y_196_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_192_);
v_a_236_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_200_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_200_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec_ref(v___y_196_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_192_);
v_a_244_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_198_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_198_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
v___jp_252_:
{
lean_object* v_fileName_258_; lean_object* v_fileMap_259_; uint8_t v_suppressElabErrors_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_279_; 
v_fileName_258_ = lean_ctor_get(v___y_186_, 0);
v_fileMap_259_ = lean_ctor_get(v___y_186_, 1);
v_suppressElabErrors_260_ = lean_ctor_get_uint8(v___y_186_, sizeof(void*)*10);
v___x_261_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_183_);
v___x_262_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v___x_261_, v___y_187_);
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_279_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_279_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_279_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_inc_ref_n(v_fileMap_259_, 2);
v___x_267_ = l_Lean_FileMap_toPosition(v_fileMap_259_, v___y_254_);
lean_dec(v___y_254_);
v___x_268_ = l_Lean_FileMap_toPosition(v_fileMap_259_, v___y_257_);
lean_dec(v___y_257_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0));
if (v_suppressElabErrors_260_ == 0)
{
lean_del_object(v___x_265_);
v___y_190_ = v___x_270_;
v___y_191_ = v___y_255_;
v___y_192_ = v___x_269_;
v___y_193_ = v___y_256_;
v___y_194_ = v_a_263_;
v___y_195_ = v_fileName_258_;
v___y_196_ = v___x_267_;
v___y_197_ = v___y_187_;
goto v___jp_189_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___f_273_; uint8_t v___x_274_; 
v___x_271_ = lean_box(v___y_253_);
v___x_272_ = lean_box(v_suppressElabErrors_260_);
v___f_273_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_273_, 0, v___x_271_);
lean_closure_set(v___f_273_, 1, v___x_272_);
lean_inc(v_a_263_);
v___x_274_ = l_Lean_MessageData_hasTag(v___f_273_, v_a_263_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_277_; 
lean_dec_ref_known(v___x_269_, 1);
lean_dec_ref(v___x_267_);
lean_dec(v_a_263_);
v___x_275_ = lean_box(0);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_275_);
v___x_277_ = v___x_265_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
else
{
lean_del_object(v___x_265_);
v___y_190_ = v___x_270_;
v___y_191_ = v___y_255_;
v___y_192_ = v___x_269_;
v___y_193_ = v___y_256_;
v___y_194_ = v_a_263_;
v___y_195_ = v_fileName_258_;
v___y_196_ = v___x_267_;
v___y_197_ = v___y_187_;
goto v___jp_189_;
}
}
}
}
v___jp_280_:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Syntax_getTailPos_x3f(v___y_284_, v___y_283_);
lean_dec(v___y_284_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_inc(v___y_285_);
v___y_253_ = v___y_281_;
v___y_254_ = v___y_285_;
v___y_255_ = v___y_282_;
v___y_256_ = v___y_283_;
v___y_257_ = v___y_285_;
goto v___jp_252_;
}
else
{
lean_object* v_val_287_; 
v_val_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_287_);
lean_dec_ref_known(v___x_286_, 1);
v___y_253_ = v___y_281_;
v___y_254_ = v___y_285_;
v___y_255_ = v___y_282_;
v___y_256_ = v___y_283_;
v___y_257_ = v_val_287_;
goto v___jp_252_;
}
}
v___jp_288_:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Elab_Command_getRef___redArg(v___y_186_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v_ref_294_; lean_object* v___x_295_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_292_, 1);
v_ref_294_ = l_Lean_replaceRef(v_ref_182_, v_a_293_);
lean_dec(v_a_293_);
v___x_295_ = l_Lean_Syntax_getPos_x3f(v_ref_294_, v___y_290_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___y_281_ = v___y_289_;
v___y_282_ = v___y_291_;
v___y_283_ = v___y_290_;
v___y_284_ = v_ref_294_;
v___y_285_ = v___x_296_;
goto v___jp_280_;
}
else
{
lean_object* v_val_297_; 
v_val_297_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v___x_295_, 1);
v___y_281_ = v___y_289_;
v___y_282_ = v___y_291_;
v___y_283_ = v___y_290_;
v___y_284_ = v_ref_294_;
v___y_285_ = v_val_297_;
goto v___jp_280_;
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v_msgData_183_);
v_a_298_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_292_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_292_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
v___jp_307_:
{
if (v___y_310_ == 0)
{
v___y_289_ = v___y_308_;
v___y_290_ = v___y_309_;
v___y_291_ = v_severity_184_;
goto v___jp_288_;
}
else
{
v___y_289_ = v___y_308_;
v___y_290_ = v___y_309_;
v___y_291_ = v___x_306_;
goto v___jp_288_;
}
}
v___jp_311_:
{
if (v___y_312_ == 0)
{
lean_object* v___x_313_; lean_object* v_scopes_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_opts_317_; uint8_t v___x_318_; uint8_t v___x_319_; 
v___x_313_ = lean_st_ref_get(v___y_187_);
v_scopes_314_ = lean_ctor_get(v___x_313_, 2);
lean_inc(v_scopes_314_);
lean_dec(v___x_313_);
v___x_315_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_316_ = l_List_head_x21___redArg(v___x_315_, v_scopes_314_);
lean_dec(v_scopes_314_);
v_opts_317_ = lean_ctor_get(v___x_316_, 1);
lean_inc_ref(v_opts_317_);
lean_dec(v___x_316_);
v___x_318_ = 1;
v___x_319_ = l_Lean_instBEqMessageSeverity_beq(v_severity_184_, v___x_318_);
if (v___x_319_ == 0)
{
lean_dec_ref(v_opts_317_);
v___y_308_ = v___y_312_;
v___y_309_ = v___y_312_;
v___y_310_ = v___x_319_;
goto v___jp_307_;
}
else
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = l_Lean_warningAsError;
v___x_321_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__11(v_opts_317_, v___x_320_);
lean_dec_ref(v_opts_317_);
v___y_308_ = v___y_312_;
v___y_309_ = v___y_312_;
v___y_310_ = v___x_321_;
goto v___jp_307_;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref(v_msgData_183_);
v___x_322_ = lean_box(0);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_ref_326_, lean_object* v_msgData_327_, lean_object* v_severity_328_, lean_object* v_isSilent_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
uint8_t v_severity_boxed_333_; uint8_t v_isSilent_boxed_334_; lean_object* v_res_335_; 
v_severity_boxed_333_ = lean_unbox(v_severity_328_);
v_isSilent_boxed_334_ = lean_unbox(v_isSilent_329_);
v_res_335_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(v_ref_326_, v_msgData_327_, v_severity_boxed_333_, v_isSilent_boxed_334_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v_ref_326_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(lean_object* v_ref_336_, lean_object* v_msgData_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
uint8_t v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; 
v___x_341_ = 1;
v___x_342_ = 0;
v___x_343_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7(v_ref_336_, v_msgData_337_, v___x_341_, v___x_342_, v___y_338_, v___y_339_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4___boxed(lean_object* v_ref_344_, lean_object* v_msgData_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(v_ref_344_, v_msgData_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v_ref_344_);
return v_res_349_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__0));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__2));
v___x_355_ = l_Lean_stringToMessageData(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(lean_object* v_linterOption_356_, lean_object* v_stx_357_, lean_object* v_msg_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_name_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_380_; 
v_name_362_ = lean_ctor_get(v_linterOption_356_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v_linterOption_356_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_linterOption_356_, 1);
lean_dec(v_unused_381_);
v___x_364_ = v_linterOption_356_;
v_isShared_365_ = v_isSharedCheck_380_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_name_362_);
lean_dec(v_linterOption_356_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_380_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__1);
lean_inc(v_name_362_);
v___x_367_ = l_Lean_MessageData_ofName(v_name_362_);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 7);
lean_ctor_set(v___x_364_, 1, v___x_367_);
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_367_);
v___x_369_ = v_reuseFailAlloc_379_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_disable_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_370_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___closed__3);
v___x_371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v_disable_372_ = l_Lean_MessageData_note(v___x_371_);
v___x_373_ = l_Lean_Linter_linterMessageTag;
v___x_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_374_, 0, v_msg_358_);
lean_ctor_set(v___x_374_, 1, v_disable_372_);
v___x_375_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_376_, 0, v_name_362_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
lean_inc(v_stx_357_);
v___x_377_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_377_, 0, v_stx_357_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(v_stx_357_, v___x_377_, v___y_359_, v___y_360_);
lean_dec(v_stx_357_);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_382_, lean_object* v_stx_383_, lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_382_, v_stx_383_, v_msg_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(lean_object* v_linterOption_389_, lean_object* v_stx_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_406_; 
v___x_395_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_392_, v___y_393_);
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_406_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_406_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_406_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
uint8_t v___x_400_; 
v___x_400_ = l_Lean_Linter_getLinterValue(v_linterOption_389_, v_a_396_);
lean_dec(v_a_396_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_403_; 
lean_dec_ref(v_msg_391_);
lean_dec(v_stx_390_);
lean_dec_ref(v_linterOption_389_);
v___x_401_ = lean_box(0);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_401_);
v___x_403_ = v___x_398_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
else
{
lean_object* v___x_405_; 
lean_del_object(v___x_398_);
v___x_405_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_389_, v_stx_390_, v_msg_391_, v___y_392_, v___y_393_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2___boxed(lean_object* v_linterOption_407_, lean_object* v_stx_408_, lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(v_linterOption_407_, v_stx_408_, v_msg_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(lean_object* v___x_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_isProp(v___x_414_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed(lean_object* v___x_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(v___x_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_431_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0));
v___x_434_ = l_Lean_stringToMessageData(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2));
v___x_437_ = l_Lean_stringToMessageData(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(lean_object* v___x_438_, uint8_t v___x_439_, lean_object* v_as_x27_440_, lean_object* v_b_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
if (lean_obj_tag(v_as_x27_440_) == 0)
{
lean_object* v___x_445_; 
lean_dec_ref(v___x_438_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v_b_441_);
return v___x_445_;
}
else
{
lean_object* v_head_446_; lean_object* v_tail_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_head_446_ = lean_ctor_get(v_as_x27_440_, 0);
v_tail_447_ = lean_ctor_get(v_as_x27_440_, 1);
v___x_448_ = lean_box(0);
lean_inc(v_head_446_);
lean_inc_ref(v___x_438_);
v___x_449_ = l_Lean_Environment_find_x3f(v___x_438_, v_head_446_, v___x_439_);
if (lean_obj_tag(v___x_449_) == 1)
{
lean_object* v_val_450_; uint8_t v___x_451_; 
v_val_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = l_Lean_ConstantInfo_isDefinition(v_val_450_);
if (v___x_451_ == 0)
{
lean_dec(v_val_450_);
v_as_x27_440_ = v_tail_447_;
v_b_441_ = v___x_448_;
goto _start;
}
else
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = l_Lean_ConstantInfo_hints(v_val_450_);
v___x_454_ = l_Lean_ReducibilityHints_isAbbrev(v___x_453_);
lean_dec(v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___f_456_; lean_object* v___x_457_; 
v___x_455_ = l_Lean_ConstantInfo_type(v_val_450_);
lean_dec(v_val_450_);
v___f_456_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_456_, 0, v___x_455_);
v___x_457_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_456_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; uint8_t v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v___x_459_ = lean_unbox(v_a_458_);
lean_dec(v_a_458_);
if (v___x_459_ == 0)
{
v_as_x27_440_ = v_tail_447_;
v_b_441_ = v___x_448_;
goto _start;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Elab_Command_getRef___redArg(v___y_442_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = l_Lean_Linter_linter_defProp;
v___x_464_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1);
lean_inc(v_head_446_);
v___x_465_ = l_Lean_MessageData_ofConstName(v_head_446_, v___x_454_);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3);
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(v___x_463_, v_a_462_, v___x_468_, v___y_442_, v___y_443_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_dec_ref_known(v___x_469_, 1);
v_as_x27_440_ = v_tail_447_;
v_b_441_ = v___x_448_;
goto _start;
}
else
{
lean_dec_ref(v___x_438_);
return v___x_469_;
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v___x_438_);
v_a_471_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_461_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_461_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
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
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec_ref(v___x_438_);
v_a_479_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_457_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_457_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_dec(v_val_450_);
v_as_x27_440_ = v_tail_447_;
v_b_441_ = v___x_448_;
goto _start;
}
}
}
else
{
lean_dec(v___x_449_);
v_as_x27_440_ = v_tail_447_;
v_b_441_ = v___x_448_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___boxed(lean_object* v___x_489_, lean_object* v___x_490_, lean_object* v_as_x27_491_, lean_object* v_b_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
uint8_t v___x_10043__boxed_496_; lean_object* v_res_497_; 
v___x_10043__boxed_496_ = lean_unbox(v___x_490_);
v_res_497_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_489_, v___x_10043__boxed_496_, v_as_x27_491_, v_b_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v_as_x27_491_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(lean_object* v___x_501_, uint8_t v___x_502_, lean_object* v_as_503_, size_t v_sz_504_, size_t v_i_505_, lean_object* v_b_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_lt(v_i_505_, v_sz_504_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec_ref(v___x_501_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v_b_506_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v_a_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec_ref(v_b_506_);
v___x_512_ = lean_box(0);
v_a_513_ = lean_array_uget_borrowed(v_as_503_, v_i_505_);
lean_inc(v_a_513_);
v___x_514_ = l_Lean_Linter_getDeclsByBody(v_a_513_);
lean_inc_ref(v___x_501_);
v___x_515_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_501_, v___x_502_, v___x_514_, v___x_512_, v___y_507_, v___y_508_);
lean_dec(v___x_514_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; size_t v___x_517_; size_t v___x_518_; 
lean_dec_ref_known(v___x_515_, 1);
v___x_516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0));
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_add(v_i_505_, v___x_517_);
v_i_505_ = v___x_518_;
v_b_506_ = v___x_516_;
goto _start;
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v___x_501_);
v_a_520_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_515_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_515_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___boxed(lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v_as_530_, lean_object* v_sz_531_, lean_object* v_i_532_, lean_object* v_b_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
uint8_t v___x_10160__boxed_537_; size_t v_sz_boxed_538_; size_t v_i_boxed_539_; lean_object* v_res_540_; 
v___x_10160__boxed_537_ = lean_unbox(v___x_529_);
v_sz_boxed_538_ = lean_unbox_usize(v_sz_531_);
lean_dec(v_sz_531_);
v_i_boxed_539_ = lean_unbox_usize(v_i_532_);
lean_dec(v_i_532_);
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_528_, v___x_10160__boxed_537_, v_as_530_, v_sz_boxed_538_, v_i_boxed_539_, v_b_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec_ref(v_as_530_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(lean_object* v___x_541_, uint8_t v___x_542_, lean_object* v_as_543_, size_t v_sz_544_, size_t v_i_545_, lean_object* v_b_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v___x_550_; 
v___x_550_ = lean_usize_dec_lt(v_i_545_, v_sz_544_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec_ref(v___x_541_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v_b_546_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v_a_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v_b_546_);
v___x_552_ = lean_box(0);
v_a_553_ = lean_array_uget_borrowed(v_as_543_, v_i_545_);
lean_inc(v_a_553_);
v___x_554_ = l_Lean_Linter_getDeclsByBody(v_a_553_);
lean_inc_ref(v___x_541_);
v___x_555_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_541_, v___x_542_, v___x_554_, v___x_552_, v___y_547_, v___y_548_);
lean_dec(v___x_554_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; size_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; 
lean_dec_ref_known(v___x_555_, 1);
v___x_556_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0));
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_545_, v___x_557_);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_541_, v___x_542_, v_as_543_, v_sz_544_, v___x_558_, v___x_556_, v___y_547_, v___y_548_);
return v___x_559_;
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec_ref(v___x_541_);
v_a_560_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_555_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_555_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9___boxed(lean_object* v___x_568_, lean_object* v___x_569_, lean_object* v_as_570_, lean_object* v_sz_571_, lean_object* v_i_572_, lean_object* v_b_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint8_t v___x_10216__boxed_577_; size_t v_sz_boxed_578_; size_t v_i_boxed_579_; lean_object* v_res_580_; 
v___x_10216__boxed_577_ = lean_unbox(v___x_569_);
v_sz_boxed_578_ = lean_unbox_usize(v_sz_571_);
lean_dec(v_sz_571_);
v_i_boxed_579_ = lean_unbox_usize(v_i_572_);
lean_dec(v_i_572_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_568_, v___x_10216__boxed_577_, v_as_570_, v_sz_boxed_578_, v_i_boxed_579_, v_b_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec_ref(v_as_570_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(lean_object* v_init_581_, lean_object* v___x_582_, uint8_t v___x_583_, lean_object* v_n_584_, lean_object* v_b_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
if (lean_obj_tag(v_n_584_) == 0)
{
lean_object* v_cs_589_; lean_object* v___x_590_; lean_object* v___x_591_; size_t v_sz_592_; size_t v___x_593_; lean_object* v___x_594_; 
v_cs_589_ = lean_ctor_get(v_n_584_, 0);
v___x_590_ = lean_box(0);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v_b_585_);
v_sz_592_ = lean_array_size(v_cs_589_);
v___x_593_ = ((size_t)0ULL);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_581_, v___x_582_, v___x_583_, v_cs_589_, v_sz_592_, v___x_593_, v___x_591_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_609_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_609_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_609_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_609_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v_fst_599_; 
v_fst_599_ = lean_ctor_get(v_a_595_, 0);
if (lean_obj_tag(v_fst_599_) == 0)
{
lean_object* v_snd_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v_snd_600_ = lean_ctor_get(v_a_595_, 1);
lean_inc(v_snd_600_);
lean_dec(v_a_595_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_snd_600_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_601_);
v___x_603_ = v___x_597_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
else
{
lean_object* v_val_605_; lean_object* v___x_607_; 
lean_inc_ref(v_fst_599_);
lean_dec(v_a_595_);
v_val_605_ = lean_ctor_get(v_fst_599_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v_fst_599_, 1);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v_val_605_);
v___x_607_ = v___x_597_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_val_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
v_a_610_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_594_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_594_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_vs_618_; lean_object* v___x_619_; lean_object* v___x_620_; size_t v_sz_621_; size_t v___x_622_; lean_object* v___x_623_; 
v_vs_618_ = lean_ctor_get(v_n_584_, 0);
v___x_619_ = lean_box(0);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v_b_585_);
v_sz_621_ = lean_array_size(v_vs_618_);
v___x_622_ = ((size_t)0ULL);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_582_, v___x_583_, v_vs_618_, v_sz_621_, v___x_622_, v___x_620_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_638_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_638_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_638_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_638_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_fst_628_; 
v_fst_628_ = lean_ctor_get(v_a_624_, 0);
if (lean_obj_tag(v_fst_628_) == 0)
{
lean_object* v_snd_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v_snd_629_ = lean_ctor_get(v_a_624_, 1);
lean_inc(v_snd_629_);
lean_dec(v_a_624_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v_snd_629_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_630_);
v___x_632_ = v___x_626_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
lean_object* v_val_634_; lean_object* v___x_636_; 
lean_inc_ref(v_fst_628_);
lean_dec(v_a_624_);
v_val_634_ = lean_ctor_get(v_fst_628_, 0);
lean_inc(v_val_634_);
lean_dec_ref_known(v_fst_628_, 1);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v_val_634_);
v___x_636_ = v___x_626_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_val_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
v_a_639_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_623_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_623_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(lean_object* v_init_647_, lean_object* v___x_648_, uint8_t v___x_649_, lean_object* v_as_650_, size_t v_sz_651_, size_t v_i_652_, lean_object* v_b_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = lean_usize_dec_lt(v_i_652_, v_sz_651_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v___x_648_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v_b_653_);
return v___x_658_;
}
else
{
lean_object* v_snd_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_693_; 
v_snd_659_ = lean_ctor_get(v_b_653_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_b_653_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v_b_653_, 0);
lean_dec(v_unused_694_);
v___x_661_ = v_b_653_;
v_isShared_662_ = v_isSharedCheck_693_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_snd_659_);
lean_dec(v_b_653_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_693_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_a_663_; lean_object* v___x_664_; 
v_a_663_ = lean_array_uget_borrowed(v_as_650_, v_i_652_);
lean_inc(v_snd_659_);
lean_inc_ref(v___x_648_);
v___x_664_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_647_, v___x_648_, v___x_649_, v_a_663_, v_snd_659_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_684_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_684_ == 0)
{
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_684_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_684_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
if (lean_obj_tag(v_a_665_) == 0)
{
lean_object* v___x_669_; lean_object* v___x_671_; 
lean_dec_ref(v___x_648_);
v___x_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_669_, 0, v_a_665_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_669_);
v___x_671_ = v___x_661_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_snd_659_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_671_);
v___x_673_ = v___x_667_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
lean_del_object(v___x_667_);
lean_dec(v_snd_659_);
v_a_676_ = lean_ctor_get(v_a_665_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v_a_665_, 1);
v___x_677_ = lean_box(0);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v_a_676_);
lean_ctor_set(v___x_661_, 0, v___x_677_);
v___x_679_ = v___x_661_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_a_676_);
v___x_679_ = v_reuseFailAlloc_683_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
size_t v___x_680_; size_t v___x_681_; 
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_add(v_i_652_, v___x_680_);
v_i_652_ = v___x_681_;
v_b_653_ = v___x_679_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_del_object(v___x_661_);
lean_dec(v_snd_659_);
lean_dec_ref(v___x_648_);
v_a_685_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_664_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_664_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8___boxed(lean_object* v_init_695_, lean_object* v___x_696_, lean_object* v___x_697_, lean_object* v_as_698_, lean_object* v_sz_699_, lean_object* v_i_700_, lean_object* v_b_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v___x_10267__boxed_705_; size_t v_sz_boxed_706_; size_t v_i_boxed_707_; lean_object* v_res_708_; 
v___x_10267__boxed_705_ = lean_unbox(v___x_697_);
v_sz_boxed_706_ = lean_unbox_usize(v_sz_699_);
lean_dec(v_sz_699_);
v_i_boxed_707_ = lean_unbox_usize(v_i_700_);
lean_dec(v_i_700_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_695_, v___x_696_, v___x_10267__boxed_705_, v_as_698_, v_sz_boxed_706_, v_i_boxed_707_, v_b_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec_ref(v_as_698_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6___boxed(lean_object* v_init_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v_n_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
uint8_t v___x_10288__boxed_717_; lean_object* v_res_718_; 
v___x_10288__boxed_717_ = lean_unbox(v___x_711_);
v_res_718_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_709_, v___x_710_, v___x_10288__boxed_717_, v_n_712_, v_b_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec_ref(v_n_712_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(lean_object* v___x_722_, uint8_t v___x_723_, lean_object* v_as_724_, size_t v_sz_725_, size_t v_i_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_lt(v_i_726_, v_sz_725_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec_ref(v___x_722_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v_b_727_);
return v___x_732_;
}
else
{
lean_object* v___x_733_; lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec_ref(v_b_727_);
v___x_733_ = lean_box(0);
v_a_734_ = lean_array_uget_borrowed(v_as_724_, v_i_726_);
lean_inc(v_a_734_);
v___x_735_ = l_Lean_Linter_getDeclsByBody(v_a_734_);
lean_inc_ref(v___x_722_);
v___x_736_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_722_, v___x_723_, v___x_735_, v___x_733_, v___y_728_, v___y_729_);
lean_dec(v___x_735_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; size_t v___x_738_; size_t v___x_739_; 
lean_dec_ref_known(v___x_736_, 1);
v___x_737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0));
v___x_738_ = ((size_t)1ULL);
v___x_739_ = lean_usize_add(v_i_726_, v___x_738_);
v_i_726_ = v___x_739_;
v_b_727_ = v___x_737_;
goto _start;
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec_ref(v___x_722_);
v_a_741_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_736_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_736_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___boxed(lean_object* v___x_749_, lean_object* v___x_750_, lean_object* v_as_751_, lean_object* v_sz_752_, lean_object* v_i_753_, lean_object* v_b_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
uint8_t v___x_10480__boxed_758_; size_t v_sz_boxed_759_; size_t v_i_boxed_760_; lean_object* v_res_761_; 
v___x_10480__boxed_758_ = lean_unbox(v___x_750_);
v_sz_boxed_759_ = lean_unbox_usize(v_sz_752_);
lean_dec(v_sz_752_);
v_i_boxed_760_ = lean_unbox_usize(v_i_753_);
lean_dec(v_i_753_);
v_res_761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_749_, v___x_10480__boxed_758_, v_as_751_, v_sz_boxed_759_, v_i_boxed_760_, v_b_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec_ref(v_as_751_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(lean_object* v___x_762_, uint8_t v___x_763_, lean_object* v_as_764_, size_t v_sz_765_, size_t v_i_766_, lean_object* v_b_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = lean_usize_dec_lt(v_i_766_, v_sz_765_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_dec_ref(v___x_762_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_b_767_);
return v___x_772_;
}
else
{
lean_object* v___x_773_; lean_object* v_a_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec_ref(v_b_767_);
v___x_773_ = lean_box(0);
v_a_774_ = lean_array_uget_borrowed(v_as_764_, v_i_766_);
lean_inc(v_a_774_);
v___x_775_ = l_Lean_Linter_getDeclsByBody(v_a_774_);
lean_inc_ref(v___x_762_);
v___x_776_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_762_, v___x_763_, v___x_775_, v___x_773_, v___y_768_, v___y_769_);
lean_dec(v___x_775_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
lean_dec_ref_known(v___x_776_, 1);
v___x_777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0));
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_add(v_i_766_, v___x_778_);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_762_, v___x_763_, v_as_764_, v_sz_765_, v___x_779_, v___x_777_, v___y_768_, v___y_769_);
return v___x_780_;
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v___x_762_);
v_a_781_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_776_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_776_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7___boxed(lean_object* v___x_789_, lean_object* v___x_790_, lean_object* v_as_791_, lean_object* v_sz_792_, lean_object* v_i_793_, lean_object* v_b_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
uint8_t v___x_10536__boxed_798_; size_t v_sz_boxed_799_; size_t v_i_boxed_800_; lean_object* v_res_801_; 
v___x_10536__boxed_798_ = lean_unbox(v___x_790_);
v_sz_boxed_799_ = lean_unbox_usize(v_sz_792_);
lean_dec(v_sz_792_);
v_i_boxed_800_ = lean_unbox_usize(v_i_793_);
lean_dec(v_i_793_);
v_res_801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_789_, v___x_10536__boxed_798_, v_as_791_, v_sz_boxed_799_, v_i_boxed_800_, v_b_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec_ref(v_as_791_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(lean_object* v___x_802_, uint8_t v___x_803_, lean_object* v_t_804_, lean_object* v_init_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_root_809_; lean_object* v_tail_810_; lean_object* v___x_811_; 
v_root_809_ = lean_ctor_get(v_t_804_, 0);
v_tail_810_ = lean_ctor_get(v_t_804_, 1);
lean_inc_ref(v___x_802_);
v___x_811_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_805_, v___x_802_, v___x_803_, v_root_809_, v_init_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_848_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_848_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_848_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_848_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
if (lean_obj_tag(v_a_812_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; 
lean_dec_ref(v___x_802_);
v_a_816_ = lean_ctor_get(v_a_812_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v_a_812_, 1);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v_a_816_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_821_; lean_object* v___x_822_; size_t v_sz_823_; size_t v___x_824_; lean_object* v___x_825_; 
lean_del_object(v___x_814_);
v_a_820_ = lean_ctor_get(v_a_812_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v_a_812_, 1);
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v_a_820_);
v_sz_823_ = lean_array_size(v_tail_810_);
v___x_824_ = ((size_t)0ULL);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_802_, v___x_803_, v_tail_810_, v_sz_823_, v___x_824_, v___x_822_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_839_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_839_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_839_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_839_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_fst_830_; 
v_fst_830_ = lean_ctor_get(v_a_826_, 0);
if (lean_obj_tag(v_fst_830_) == 0)
{
lean_object* v_snd_831_; lean_object* v___x_833_; 
v_snd_831_ = lean_ctor_get(v_a_826_, 1);
lean_inc(v_snd_831_);
lean_dec(v_a_826_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_snd_831_);
v___x_833_ = v___x_828_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_snd_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v_val_835_; lean_object* v___x_837_; 
lean_inc_ref(v_fst_830_);
lean_dec(v_a_826_);
v_val_835_ = lean_ctor_get(v_fst_830_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v_fst_830_, 1);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_val_835_);
v___x_837_ = v___x_828_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_val_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_825_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_825_);
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
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v___x_802_);
v_a_849_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_811_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_811_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4___boxed(lean_object* v___x_857_, lean_object* v___x_858_, lean_object* v_t_859_, lean_object* v_init_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
uint8_t v___x_10587__boxed_864_; lean_object* v_res_865_; 
v___x_10587__boxed_864_ = lean_unbox(v___x_858_);
v_res_865_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(v___x_857_, v___x_10587__boxed_864_, v_t_859_, v_init_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec_ref(v_t_859_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DefProp_defPropLinter___lam__0(lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_902_; 
v___x_870_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_867_, v___y_868_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_902_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_902_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_902_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = l_Lean_Linter_linter_defProp;
v___x_876_ = l_Lean_Linter_getLinterValue(v___x_875_, v_a_871_);
lean_dec(v_a_871_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = lean_box(0);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_879_ = v___x_873_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
lean_object* v___x_881_; lean_object* v_messages_882_; uint8_t v___x_883_; 
v___x_881_ = lean_st_ref_get(v___y_868_);
v_messages_882_ = lean_ctor_get(v___x_881_, 1);
lean_inc_ref(v_messages_882_);
lean_dec(v___x_881_);
v___x_883_ = l_Lean_MessageLog_hasErrors(v_messages_882_);
lean_dec_ref(v_messages_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v_env_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_del_object(v___x_873_);
v___x_884_ = lean_st_ref_get(v___y_868_);
v___x_885_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(v___y_868_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref(v___x_885_);
v_env_887_ = lean_ctor_get(v___x_884_, 0);
lean_inc_ref(v_env_887_);
lean_dec(v___x_884_);
v___x_888_ = lean_box(0);
v___x_889_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(v_env_887_, v___x_883_, v_a_886_, v___x_888_, v___y_867_, v___y_868_);
lean_dec(v_a_886_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v___x_889_, 0);
lean_dec(v_unused_897_);
v___x_891_ = v___x_889_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_dec(v___x_889_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_888_);
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_888_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
return v___x_889_;
}
}
else
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_box(0);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_898_);
v___x_900_ = v___x_873_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DefProp_defPropLinter___lam__0___boxed(lean_object* v_x_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Linter_DefProp_defPropLinter___lam__0(v_x_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v_x_903_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(lean_object* v_o_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_o_922_, v___y_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___boxed(lean_object* v_o_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(v_o_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(lean_object* v___x_932_, uint8_t v___x_933_, lean_object* v_as_934_, lean_object* v_as_x27_935_, lean_object* v_b_936_, lean_object* v_a_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_932_, v___x_933_, v_as_x27_935_, v_b_936_, v___y_938_, v___y_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___boxed(lean_object* v___x_942_, lean_object* v___x_943_, lean_object* v_as_944_, lean_object* v_as_x27_945_, lean_object* v_b_946_, lean_object* v_a_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
uint8_t v___x_10820__boxed_951_; lean_object* v_res_952_; 
v___x_10820__boxed_951_ = lean_unbox(v___x_943_);
v_res_952_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(v___x_942_, v___x_10820__boxed_951_, v_as_944_, v_as_x27_945_, v_b_946_, v_a_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v_as_x27_945_);
lean_dec(v_as_944_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_msgData_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_msgData_953_, v___y_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_msgData_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(v_msgData_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_Linter_DefProp_defPropLinter));
v___x_965_ = l_Lean_Elab_Command_addLinter(v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2____boxed(lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_();
return v_res_967_;
}
}
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_DefProp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
