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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Linter_getDeclsByBody(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isDefinition(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "defProp"};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 155, 102, 62, 63, 148, 150, 28)}};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 175, .m_capacity = 175, .m_length = 174, .m_data = "enable the `defProp` linter, which warns when a `def` is used to introduce a declaration whose type is a `Prop`; such a declaration should be written using `theorem` instead."};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(11, 14, 230, 184, 252, 64, 196, 245)}};
static const lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_DefProp_defPropLinter___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_();
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
uint8_t v___y_9120__boxed_125_; uint8_t v_suppressElabErrors_boxed_126_; uint8_t v_res_127_; lean_object* v_r_128_; 
v___y_9120__boxed_125_ = lean_unbox(v___y_122_);
v_suppressElabErrors_boxed_126_ = lean_unbox(v_suppressElabErrors_123_);
v_res_127_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___lam__0(v___y_9120__boxed_125_, v_suppressElabErrors_boxed_126_, v_x_124_);
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
uint8_t v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; uint8_t v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; uint8_t v___y_253_; uint8_t v___y_254_; lean_object* v___y_255_; uint8_t v___y_256_; lean_object* v___y_257_; uint8_t v___y_281_; uint8_t v___y_282_; uint8_t v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; uint8_t v___y_289_; uint8_t v___y_290_; uint8_t v___y_291_; uint8_t v___x_306_; uint8_t v___y_308_; uint8_t v___y_309_; uint8_t v___y_310_; uint8_t v___y_312_; uint8_t v___x_324_; 
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
lean_ctor_set(v___x_223_, 1, v___y_191_);
lean_inc_ref(v___y_193_);
lean_inc_ref(v___y_196_);
v___x_224_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_224_, 0, v___y_196_);
lean_ctor_set(v___x_224_, 1, v___y_195_);
lean_ctor_set(v___x_224_, 2, v___y_192_);
lean_ctor_set(v___x_224_, 3, v___y_193_);
lean_ctor_set(v___x_224_, 4, v___x_223_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*5, v___y_194_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*5 + 1, v___y_190_);
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
lean_dec_ref(v___y_195_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
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
lean_dec_ref(v___y_195_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
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
v___x_267_ = l_Lean_FileMap_toPosition(v_fileMap_259_, v___y_255_);
lean_dec(v___y_255_);
v___x_268_ = l_Lean_FileMap_toPosition(v_fileMap_259_, v___y_257_);
lean_dec(v___y_257_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
v___x_270_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7___closed__0));
if (v_suppressElabErrors_260_ == 0)
{
lean_del_object(v___x_265_);
v___y_190_ = v___y_254_;
v___y_191_ = v_a_263_;
v___y_192_ = v___x_269_;
v___y_193_ = v___x_270_;
v___y_194_ = v___y_256_;
v___y_195_ = v___x_267_;
v___y_196_ = v_fileName_258_;
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
v___y_190_ = v___y_254_;
v___y_191_ = v_a_263_;
v___y_192_ = v___x_269_;
v___y_193_ = v___x_270_;
v___y_194_ = v___y_256_;
v___y_195_ = v___x_267_;
v___y_196_ = v_fileName_258_;
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
v___y_254_ = v___y_282_;
v___y_255_ = v___y_285_;
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
v___y_254_ = v___y_282_;
v___y_255_ = v___y_285_;
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
lean_object* v_name_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_379_; 
v_name_362_ = lean_ctor_get(v_linterOption_356_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_linterOption_356_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v_linterOption_356_, 1);
lean_dec(v_unused_380_);
v___x_364_ = v_linterOption_356_;
v_isShared_365_ = v_isSharedCheck_379_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_name_362_);
lean_dec(v_linterOption_356_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_379_;
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
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_367_);
v___x_369_ = v_reuseFailAlloc_378_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_disable_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
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
v___x_377_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4(v_stx_357_, v___x_376_, v___y_359_, v___y_360_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3___boxed(lean_object* v_linterOption_381_, lean_object* v_stx_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_381_, v_stx_382_, v_msg_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v_stx_382_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(lean_object* v_linterOption_388_, lean_object* v_stx_389_, lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_405_; 
v___x_394_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_391_, v___y_392_);
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_405_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
uint8_t v___x_399_; 
v___x_399_ = l_Lean_Linter_getLinterValue(v_linterOption_388_, v_a_395_);
lean_dec(v_a_395_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_402_; 
lean_dec_ref(v_msg_390_);
lean_dec_ref(v_linterOption_388_);
v___x_400_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_400_);
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
else
{
lean_object* v___x_404_; 
lean_del_object(v___x_397_);
v___x_404_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3(v_linterOption_388_, v_stx_389_, v_msg_390_, v___y_391_, v___y_392_);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2___boxed(lean_object* v_linterOption_406_, lean_object* v_stx_407_, lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(v_linterOption_406_, v_stx_407_, v_msg_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v_stx_407_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(lean_object* v___x_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Meta_isProp(v___x_413_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed(lean_object* v___x_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0(v___x_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_430_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__0));
v___x_433_ = l_Lean_stringToMessageData(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__2));
v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(lean_object* v___x_437_, uint8_t v___x_438_, lean_object* v_as_x27_439_, lean_object* v_b_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
if (lean_obj_tag(v_as_x27_439_) == 0)
{
lean_object* v___x_444_; 
lean_dec_ref(v___x_437_);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v_b_440_);
return v___x_444_;
}
else
{
lean_object* v_head_445_; lean_object* v_tail_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_head_445_ = lean_ctor_get(v_as_x27_439_, 0);
v_tail_446_ = lean_ctor_get(v_as_x27_439_, 1);
v___x_447_ = lean_box(0);
lean_inc(v_head_445_);
lean_inc_ref(v___x_437_);
v___x_448_ = l_Lean_Environment_find_x3f(v___x_437_, v_head_445_, v___x_438_);
if (lean_obj_tag(v___x_448_) == 1)
{
lean_object* v_val_449_; uint8_t v___x_450_; 
v_val_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v___x_448_, 1);
v___x_450_ = l_Lean_ConstantInfo_isDefinition(v_val_449_);
if (v___x_450_ == 0)
{
lean_dec(v_val_449_);
v_as_x27_439_ = v_tail_446_;
v_b_440_ = v___x_447_;
goto _start;
}
else
{
lean_object* v___x_452_; lean_object* v___f_453_; lean_object* v___x_454_; 
v___x_452_ = l_Lean_ConstantInfo_type(v_val_449_);
lean_dec(v_val_449_);
v___f_453_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_453_, 0, v___x_452_);
v___x_454_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_453_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; uint8_t v___x_456_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v___x_456_ = lean_unbox(v_a_455_);
lean_dec(v_a_455_);
if (v___x_456_ == 0)
{
v_as_x27_439_ = v_tail_446_;
v_b_440_ = v___x_447_;
goto _start;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Elab_Command_getRef___redArg(v___y_441_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = l_Lean_Linter_linter_defProp;
v___x_461_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__1);
lean_inc(v_head_445_);
v___x_462_ = l_Lean_MessageData_ofConstName(v_head_445_, v___x_438_);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___closed__3);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2(v___x_460_, v_a_459_, v___x_465_, v___y_441_, v___y_442_);
lean_dec(v_a_459_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_dec_ref_known(v___x_466_, 1);
v_as_x27_439_ = v_tail_446_;
v_b_440_ = v___x_447_;
goto _start;
}
else
{
lean_dec_ref(v___x_437_);
return v___x_466_;
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec_ref(v___x_437_);
v_a_468_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_458_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_458_);
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
lean_dec_ref(v___x_437_);
v_a_476_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_454_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_454_);
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
}
else
{
lean_dec(v___x_448_);
v_as_x27_439_ = v_tail_446_;
v_b_440_ = v___x_447_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg___boxed(lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v_as_x27_487_, lean_object* v_b_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
uint8_t v___x_9646__boxed_492_; lean_object* v_res_493_; 
v___x_9646__boxed_492_ = lean_unbox(v___x_486_);
v_res_493_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_485_, v___x_9646__boxed_492_, v_as_x27_487_, v_b_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v_as_x27_487_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(lean_object* v___x_497_, uint8_t v___x_498_, lean_object* v_as_499_, size_t v_sz_500_, size_t v_i_501_, lean_object* v_b_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_lt(v_i_501_, v_sz_500_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
lean_dec_ref(v___x_497_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v_b_502_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; lean_object* v_a_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec_ref(v_b_502_);
v___x_508_ = lean_box(0);
v_a_509_ = lean_array_uget_borrowed(v_as_499_, v_i_501_);
lean_inc(v_a_509_);
v___x_510_ = l_Lean_Linter_getDeclsByBody(v_a_509_);
lean_inc_ref(v___x_497_);
v___x_511_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_497_, v___x_498_, v___x_510_, v___x_508_, v___y_503_, v___y_504_);
lean_dec(v___x_510_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v___x_512_; size_t v___x_513_; size_t v___x_514_; 
lean_dec_ref_known(v___x_511_, 1);
v___x_512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0));
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_add(v_i_501_, v___x_513_);
v_i_501_ = v___x_514_;
v_b_502_ = v___x_512_;
goto _start;
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec_ref(v___x_497_);
v_a_516_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_511_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_511_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___boxed(lean_object* v___x_524_, lean_object* v___x_525_, lean_object* v_as_526_, lean_object* v_sz_527_, lean_object* v_i_528_, lean_object* v_b_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
uint8_t v___x_9757__boxed_533_; size_t v_sz_boxed_534_; size_t v_i_boxed_535_; lean_object* v_res_536_; 
v___x_9757__boxed_533_ = lean_unbox(v___x_525_);
v_sz_boxed_534_ = lean_unbox_usize(v_sz_527_);
lean_dec(v_sz_527_);
v_i_boxed_535_ = lean_unbox_usize(v_i_528_);
lean_dec(v_i_528_);
v_res_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_524_, v___x_9757__boxed_533_, v_as_526_, v_sz_boxed_534_, v_i_boxed_535_, v_b_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_as_526_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(lean_object* v___x_537_, uint8_t v___x_538_, lean_object* v_as_539_, size_t v_sz_540_, size_t v_i_541_, lean_object* v_b_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
uint8_t v___x_546_; 
v___x_546_ = lean_usize_dec_lt(v_i_541_, v_sz_540_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
lean_dec_ref(v___x_537_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v_b_542_);
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v_a_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec_ref(v_b_542_);
v___x_548_ = lean_box(0);
v_a_549_ = lean_array_uget_borrowed(v_as_539_, v_i_541_);
lean_inc(v_a_549_);
v___x_550_ = l_Lean_Linter_getDeclsByBody(v_a_549_);
lean_inc_ref(v___x_537_);
v___x_551_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_537_, v___x_538_, v___x_550_, v___x_548_, v___y_543_, v___y_544_);
lean_dec(v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v___x_552_; size_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; 
lean_dec_ref_known(v___x_551_, 1);
v___x_552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11___closed__0));
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_add(v_i_541_, v___x_553_);
v___x_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9_spec__11(v___x_537_, v___x_538_, v_as_539_, v_sz_540_, v___x_554_, v___x_552_, v___y_543_, v___y_544_);
return v___x_555_;
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v___x_537_);
v_a_556_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_551_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_551_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9___boxed(lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v_as_566_, lean_object* v_sz_567_, lean_object* v_i_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
uint8_t v___x_9813__boxed_573_; size_t v_sz_boxed_574_; size_t v_i_boxed_575_; lean_object* v_res_576_; 
v___x_9813__boxed_573_ = lean_unbox(v___x_565_);
v_sz_boxed_574_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v_i_boxed_575_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_564_, v___x_9813__boxed_573_, v_as_566_, v_sz_boxed_574_, v_i_boxed_575_, v_b_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v_as_566_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(lean_object* v_init_577_, lean_object* v___x_578_, uint8_t v___x_579_, lean_object* v_n_580_, lean_object* v_b_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
if (lean_obj_tag(v_n_580_) == 0)
{
lean_object* v_cs_585_; lean_object* v___x_586_; lean_object* v___x_587_; size_t v_sz_588_; size_t v___x_589_; lean_object* v___x_590_; 
v_cs_585_ = lean_ctor_get(v_n_580_, 0);
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v_b_581_);
v_sz_588_ = lean_array_size(v_cs_585_);
v___x_589_ = ((size_t)0ULL);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_577_, v___x_578_, v___x_579_, v_cs_585_, v_sz_588_, v___x_589_, v___x_587_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_605_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_605_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_605_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_605_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_fst_595_; 
v_fst_595_ = lean_ctor_get(v_a_591_, 0);
if (lean_obj_tag(v_fst_595_) == 0)
{
lean_object* v_snd_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v_snd_596_ = lean_ctor_get(v_a_591_, 1);
lean_inc(v_snd_596_);
lean_dec(v_a_591_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_snd_596_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_597_);
v___x_599_ = v___x_593_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v_val_601_; lean_object* v___x_603_; 
lean_inc_ref(v_fst_595_);
lean_dec(v_a_591_);
v_val_601_ = lean_ctor_get(v_fst_595_, 0);
lean_inc(v_val_601_);
lean_dec_ref_known(v_fst_595_, 1);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v_val_601_);
v___x_603_ = v___x_593_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_val_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
v_a_606_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_590_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_590_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_vs_614_; lean_object* v___x_615_; lean_object* v___x_616_; size_t v_sz_617_; size_t v___x_618_; lean_object* v___x_619_; 
v_vs_614_ = lean_ctor_get(v_n_580_, 0);
v___x_615_ = lean_box(0);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_b_581_);
v_sz_617_ = lean_array_size(v_vs_614_);
v___x_618_ = ((size_t)0ULL);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__9(v___x_578_, v___x_579_, v_vs_614_, v_sz_617_, v___x_618_, v___x_616_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_634_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_634_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_634_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_634_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_fst_624_; 
v_fst_624_ = lean_ctor_get(v_a_620_, 0);
if (lean_obj_tag(v_fst_624_) == 0)
{
lean_object* v_snd_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v_snd_625_ = lean_ctor_get(v_a_620_, 1);
lean_inc(v_snd_625_);
lean_dec(v_a_620_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v_snd_625_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_626_);
v___x_628_ = v___x_622_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
else
{
lean_object* v_val_630_; lean_object* v___x_632_; 
lean_inc_ref(v_fst_624_);
lean_dec(v_a_620_);
v_val_630_ = lean_ctor_get(v_fst_624_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v_fst_624_, 1);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v_val_630_);
v___x_632_ = v___x_622_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_val_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_a_635_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_619_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_619_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(lean_object* v_init_643_, lean_object* v___x_644_, uint8_t v___x_645_, lean_object* v_as_646_, size_t v_sz_647_, size_t v_i_648_, lean_object* v_b_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
uint8_t v___x_653_; 
v___x_653_ = lean_usize_dec_lt(v_i_648_, v_sz_647_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref(v___x_644_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v_b_649_);
return v___x_654_;
}
else
{
lean_object* v_snd_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_689_; 
v_snd_655_ = lean_ctor_get(v_b_649_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_b_649_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; 
v_unused_690_ = lean_ctor_get(v_b_649_, 0);
lean_dec(v_unused_690_);
v___x_657_ = v_b_649_;
v_isShared_658_ = v_isSharedCheck_689_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snd_655_);
lean_dec(v_b_649_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_689_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_a_659_; lean_object* v___x_660_; 
v_a_659_ = lean_array_uget_borrowed(v_as_646_, v_i_648_);
lean_inc(v_snd_655_);
lean_inc_ref(v___x_644_);
v___x_660_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_643_, v___x_644_, v___x_645_, v_a_659_, v_snd_655_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_680_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_680_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_680_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_680_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
if (lean_obj_tag(v_a_661_) == 0)
{
lean_object* v___x_665_; lean_object* v___x_667_; 
lean_dec_ref(v___x_644_);
v___x_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_665_, 0, v_a_661_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_665_);
v___x_667_ = v___x_657_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_snd_655_);
v___x_667_ = v_reuseFailAlloc_671_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_667_);
v___x_669_ = v___x_663_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
lean_del_object(v___x_663_);
lean_dec(v_snd_655_);
v_a_672_ = lean_ctor_get(v_a_661_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v_a_661_, 1);
v___x_673_ = lean_box(0);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_a_672_);
lean_ctor_set(v___x_657_, 0, v___x_673_);
v___x_675_ = v___x_657_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_a_672_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
size_t v___x_676_; size_t v___x_677_; 
v___x_676_ = ((size_t)1ULL);
v___x_677_ = lean_usize_add(v_i_648_, v___x_676_);
v_i_648_ = v___x_677_;
v_b_649_ = v___x_675_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_del_object(v___x_657_);
lean_dec(v_snd_655_);
lean_dec_ref(v___x_644_);
v_a_681_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_660_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_660_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8___boxed(lean_object* v_init_691_, lean_object* v___x_692_, lean_object* v___x_693_, lean_object* v_as_694_, lean_object* v_sz_695_, lean_object* v_i_696_, lean_object* v_b_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
uint8_t v___x_9864__boxed_701_; size_t v_sz_boxed_702_; size_t v_i_boxed_703_; lean_object* v_res_704_; 
v___x_9864__boxed_701_ = lean_unbox(v___x_693_);
v_sz_boxed_702_ = lean_unbox_usize(v_sz_695_);
lean_dec(v_sz_695_);
v_i_boxed_703_ = lean_unbox_usize(v_i_696_);
lean_dec(v_i_696_);
v_res_704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6_spec__8(v_init_691_, v___x_692_, v___x_9864__boxed_701_, v_as_694_, v_sz_boxed_702_, v_i_boxed_703_, v_b_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_as_694_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6___boxed(lean_object* v_init_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v_n_708_, lean_object* v_b_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_9885__boxed_713_; lean_object* v_res_714_; 
v___x_9885__boxed_713_ = lean_unbox(v___x_707_);
v_res_714_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_705_, v___x_706_, v___x_9885__boxed_713_, v_n_708_, v_b_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_n_708_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(lean_object* v___x_718_, uint8_t v___x_719_, lean_object* v_as_720_, size_t v_sz_721_, size_t v_i_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
uint8_t v___x_727_; 
v___x_727_ = lean_usize_dec_lt(v_i_722_, v_sz_721_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
lean_dec_ref(v___x_718_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v_b_723_);
return v___x_728_;
}
else
{
lean_object* v___x_729_; lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec_ref(v_b_723_);
v___x_729_ = lean_box(0);
v_a_730_ = lean_array_uget_borrowed(v_as_720_, v_i_722_);
lean_inc(v_a_730_);
v___x_731_ = l_Lean_Linter_getDeclsByBody(v_a_730_);
lean_inc_ref(v___x_718_);
v___x_732_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_718_, v___x_719_, v___x_731_, v___x_729_, v___y_724_, v___y_725_);
lean_dec(v___x_731_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v___x_733_; size_t v___x_734_; size_t v___x_735_; 
lean_dec_ref_known(v___x_732_, 1);
v___x_733_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0));
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_722_, v___x_734_);
v_i_722_ = v___x_735_;
v_b_723_ = v___x_733_;
goto _start;
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v___x_718_);
v_a_737_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_732_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_732_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___boxed(lean_object* v___x_745_, lean_object* v___x_746_, lean_object* v_as_747_, lean_object* v_sz_748_, lean_object* v_i_749_, lean_object* v_b_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
uint8_t v___x_10077__boxed_754_; size_t v_sz_boxed_755_; size_t v_i_boxed_756_; lean_object* v_res_757_; 
v___x_10077__boxed_754_ = lean_unbox(v___x_746_);
v_sz_boxed_755_ = lean_unbox_usize(v_sz_748_);
lean_dec(v_sz_748_);
v_i_boxed_756_ = lean_unbox_usize(v_i_749_);
lean_dec(v_i_749_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_745_, v___x_10077__boxed_754_, v_as_747_, v_sz_boxed_755_, v_i_boxed_756_, v_b_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec_ref(v_as_747_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(lean_object* v___x_758_, uint8_t v___x_759_, lean_object* v_as_760_, size_t v_sz_761_, size_t v_i_762_, lean_object* v_b_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
uint8_t v___x_767_; 
v___x_767_ = lean_usize_dec_lt(v_i_762_, v_sz_761_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_dec_ref(v___x_758_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v_b_763_);
return v___x_768_;
}
else
{
lean_object* v___x_769_; lean_object* v_a_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec_ref(v_b_763_);
v___x_769_ = lean_box(0);
v_a_770_ = lean_array_uget_borrowed(v_as_760_, v_i_762_);
lean_inc(v_a_770_);
v___x_771_ = l_Lean_Linter_getDeclsByBody(v_a_770_);
lean_inc_ref(v___x_758_);
v___x_772_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_758_, v___x_759_, v___x_771_, v___x_769_, v___y_764_, v___y_765_);
lean_dec(v___x_771_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v___x_773_; size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
lean_dec_ref_known(v___x_772_, 1);
v___x_773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11___closed__0));
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_762_, v___x_774_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7_spec__11(v___x_758_, v___x_759_, v_as_760_, v_sz_761_, v___x_775_, v___x_773_, v___y_764_, v___y_765_);
return v___x_776_;
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v___x_758_);
v_a_777_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_772_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_772_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7___boxed(lean_object* v___x_785_, lean_object* v___x_786_, lean_object* v_as_787_, lean_object* v_sz_788_, lean_object* v_i_789_, lean_object* v_b_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v___x_10133__boxed_794_; size_t v_sz_boxed_795_; size_t v_i_boxed_796_; lean_object* v_res_797_; 
v___x_10133__boxed_794_ = lean_unbox(v___x_786_);
v_sz_boxed_795_ = lean_unbox_usize(v_sz_788_);
lean_dec(v_sz_788_);
v_i_boxed_796_ = lean_unbox_usize(v_i_789_);
lean_dec(v_i_789_);
v_res_797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_785_, v___x_10133__boxed_794_, v_as_787_, v_sz_boxed_795_, v_i_boxed_796_, v_b_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec_ref(v_as_787_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(lean_object* v___x_798_, uint8_t v___x_799_, lean_object* v_t_800_, lean_object* v_init_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_root_805_; lean_object* v_tail_806_; lean_object* v___x_807_; 
v_root_805_ = lean_ctor_get(v_t_800_, 0);
v_tail_806_ = lean_ctor_get(v_t_800_, 1);
lean_inc_ref(v___x_798_);
v___x_807_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__6(v_init_801_, v___x_798_, v___x_799_, v_root_805_, v_init_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_844_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_844_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_844_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_844_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
if (lean_obj_tag(v_a_808_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; 
lean_dec_ref(v___x_798_);
v_a_812_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v_a_808_, 1);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v_a_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_817_; lean_object* v___x_818_; size_t v_sz_819_; size_t v___x_820_; lean_object* v___x_821_; 
lean_del_object(v___x_810_);
v_a_816_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v_a_808_, 1);
v___x_817_ = lean_box(0);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v_a_816_);
v_sz_819_ = lean_array_size(v_tail_806_);
v___x_820_ = ((size_t)0ULL);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4_spec__7(v___x_798_, v___x_799_, v_tail_806_, v_sz_819_, v___x_820_, v___x_818_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_835_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_835_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_835_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_835_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_fst_826_; 
v_fst_826_ = lean_ctor_get(v_a_822_, 0);
if (lean_obj_tag(v_fst_826_) == 0)
{
lean_object* v_snd_827_; lean_object* v___x_829_; 
v_snd_827_ = lean_ctor_get(v_a_822_, 1);
lean_inc(v_snd_827_);
lean_dec(v_a_822_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_snd_827_);
v___x_829_ = v___x_824_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_snd_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
lean_object* v_val_831_; lean_object* v___x_833_; 
lean_inc_ref(v_fst_826_);
lean_dec(v_a_822_);
v_val_831_ = lean_ctor_get(v_fst_826_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v_fst_826_, 1);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_val_831_);
v___x_833_ = v___x_824_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_val_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_821_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_821_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec_ref(v___x_798_);
v_a_845_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_807_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_807_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4___boxed(lean_object* v___x_853_, lean_object* v___x_854_, lean_object* v_t_855_, lean_object* v_init_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v___x_10184__boxed_860_; lean_object* v_res_861_; 
v___x_10184__boxed_860_ = lean_unbox(v___x_854_);
v_res_861_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(v___x_853_, v___x_10184__boxed_860_, v_t_855_, v_init_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v_t_855_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DefProp_defPropLinter___lam__0(lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_898_; 
v___x_866_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0(v___y_863_, v___y_864_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_898_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_898_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_898_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = l_Lean_Linter_linter_defProp;
v___x_872_ = l_Lean_Linter_getLinterValue(v___x_871_, v_a_867_);
lean_dec(v_a_867_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = lean_box(0);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_873_);
v___x_875_ = v___x_869_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
else
{
lean_object* v___x_877_; lean_object* v_messages_878_; uint8_t v___x_879_; 
v___x_877_ = lean_st_ref_get(v___y_864_);
v_messages_878_ = lean_ctor_get(v___x_877_, 1);
lean_inc_ref(v_messages_878_);
lean_dec(v___x_877_);
v___x_879_ = l_Lean_MessageLog_hasErrors(v_messages_878_);
lean_dec_ref(v_messages_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_a_882_; lean_object* v_env_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_del_object(v___x_869_);
v___x_880_ = lean_st_ref_get(v___y_864_);
v___x_881_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_DefProp_defPropLinter_spec__1___redArg(v___y_864_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref(v___x_881_);
v_env_883_ = lean_ctor_get(v___x_880_, 0);
lean_inc_ref(v_env_883_);
lean_dec(v___x_880_);
v___x_884_ = lean_box(0);
v___x_885_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_DefProp_defPropLinter_spec__4(v_env_883_, v___x_879_, v_a_882_, v___x_884_, v___y_863_, v___y_864_);
lean_dec(v_a_882_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_885_, 0);
lean_dec(v_unused_893_);
v___x_887_ = v___x_885_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_dec(v___x_885_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_884_);
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_884_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
return v___x_885_;
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = lean_box(0);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_894_);
v___x_896_ = v___x_869_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_DefProp_defPropLinter___lam__0___boxed(lean_object* v_x_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Linter_DefProp_defPropLinter___lam__0(v_x_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v_x_899_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(lean_object* v_o_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___redArg(v_o_918_, v___y_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0___boxed(lean_object* v_o_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_DefProp_defPropLinter_spec__0_spec__0(v_o_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(lean_object* v___x_928_, uint8_t v___x_929_, lean_object* v_as_930_, lean_object* v_as_x27_931_, lean_object* v_b_932_, lean_object* v_a_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___redArg(v___x_928_, v___x_929_, v_as_x27_931_, v_b_932_, v___y_934_, v___y_935_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3___boxed(lean_object* v___x_938_, lean_object* v___x_939_, lean_object* v_as_940_, lean_object* v_as_x27_941_, lean_object* v_b_942_, lean_object* v_a_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v___x_10417__boxed_947_; lean_object* v_res_948_; 
v___x_10417__boxed_947_ = lean_unbox(v___x_939_);
v_res_948_ = l_List_forIn_x27_loop___at___00Lean_Linter_DefProp_defPropLinter_spec__3(v___x_938_, v___x_10417__boxed_947_, v_as_940_, v_as_x27_941_, v_b_942_, v_a_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v_as_x27_941_);
lean_dec(v_as_940_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_msgData_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_msgData_949_, v___y_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_msgData_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Linter_DefProp_defPropLinter_spec__2_spec__3_spec__4_spec__7_spec__10(v_msgData_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_Linter_DefProp_defPropLinter));
v___x_961_ = l_Lean_Elab_Command_addLinter(v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2____boxed(lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Linter_DefProp_0__Lean_Linter_DefProp_initFn_00___x40_Lean_Linter_DefProp_3668228144____hygCtx___hyg_2_();
return v_res_963_;
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
res = l___private_Lean_Linter_DefProp_0__Lean_Linter_initFn_00___x40_Lean_Linter_DefProp_1144434839____hygCtx___hyg_4_();
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
