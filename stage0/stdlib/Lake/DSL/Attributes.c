// Lean compiler output
// Module: Lake.DSL.Attributes
// Imports: public import Lake.DSL.AttributesCore
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lake_testDriverAttr;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "@[test_runner] has been deprecated, use @[test_driver] instead"};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__3_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 223, 152, 205, 91, 21, 95, 180)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__3_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__3_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__4_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "DSL"};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__4_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__4_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__5_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__3_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__4_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(20, 230, 244, 102, 183, 225, 161, 156)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__5_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__5_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__6_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Attributes"};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__6_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__6_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__7_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__5_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__6_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(21, 112, 35, 119, 92, 62, 33, 243)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__7_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__7_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__8_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__7_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(128, 215, 104, 200, 157, 168, 78, 94)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__8_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__8_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__9_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__8_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 228, 88, 128, 18, 233, 225, 124)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__9_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__9_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__10_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__10_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__10_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__11_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__9_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__10_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 115, 167, 0, 56, 125, 244, 121)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__11_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__11_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__12_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__12_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__12_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__13_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__11_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__12_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 114, 109, 180, 162, 204, 4, 5)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__13_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__13_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__14_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__13_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(240, 60, 239, 76, 71, 145, 25, 107)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__14_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__14_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__15_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__14_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__4_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 246, 90, 170, 55, 7, 186, 229)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__15_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__15_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__16_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__15_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__6_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 210, 98, 154, 5, 175, 213, 120)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__16_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__16_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__17_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__16_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)(((size_t)(945171751) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(106, 161, 129, 97, 165, 63, 51, 113)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__17_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__17_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__18_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__18_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__18_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__19_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__17_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__18_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 45, 176, 97, 198, 122, 187, 200)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__19_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__19_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__20_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__20_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__20_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__21_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__19_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__20_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 1, 114, 14, 172, 231, 251, 104)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__21_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__21_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__21_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(136, 25, 248, 207, 71, 73, 30, 97)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__23_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "test_runner"};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__23_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__23_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__23_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(71, 60, 143, 185, 12, 221, 130, 16)}};
static const lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v___x_5_);
lean_ctor_set(v___x_6_, 3, v___x_5_);
lean_ctor_set(v___x_6_, 4, v___x_4_);
lean_ctor_set(v___x_6_, 5, v___x_4_);
lean_ctor_set(v___x_6_, 6, v___x_4_);
lean_ctor_set(v___x_6_, 7, v___x_4_);
lean_ctor_set(v___x_6_, 8, v___x_4_);
lean_ctor_set(v___x_6_, 9, v___x_4_);
lean_ctor_set(v___x_6_, 10, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = lean_unsigned_to_nat(32u);
v___x_8_ = lean_mk_empty_array_with_capacity(v___x_7_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_10_ = ((size_t)5ULL);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_unsigned_to_nat(32u);
v___x_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
v___x_14_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3);
v___x_15_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_11_);
lean_ctor_set(v___x_15_, 3, v___x_11_);
lean_ctor_set_usize(v___x_15_, 4, v___x_10_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = lean_box(1);
v___x_17_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1);
v___x_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
lean_ctor_set(v___x_19_, 2, v___x_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; lean_object* v_toCold_25_; lean_object* v_env_26_; lean_object* v_options_27_; uint8_t v___x_28_; lean_object* v_env_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_toCold_25_ = lean_ctor_get(v___y_21_, 0);
v_env_26_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_24_);
v_options_27_ = lean_ctor_get(v_toCold_25_, 2);
v___x_28_ = 0;
v_env_29_ = l_Lean_Environment_setRecordingDeps(v_env_26_, v___x_28_);
v___x_30_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2);
v___x_31_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_27_);
v___x_32_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_32_, 0, v_env_29_);
lean_ctor_set(v___x_32_, 1, v___x_30_);
lean_ctor_set(v___x_32_, 2, v___x_31_);
lean_ctor_set(v___x_32_, 3, v_options_27_);
v___x_33_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v_msgData_20_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_msgData_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_39_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_opts_40_, lean_object* v_opt_41_){
_start:
{
lean_object* v_name_42_; lean_object* v_defValue_43_; lean_object* v_map_44_; lean_object* v___x_45_; 
v_name_42_ = lean_ctor_get(v_opt_41_, 0);
v_defValue_43_ = lean_ctor_get(v_opt_41_, 1);
v_map_44_ = lean_ctor_get(v_opts_40_, 0);
v___x_45_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_44_, v_name_42_);
if (lean_obj_tag(v___x_45_) == 0)
{
uint8_t v___x_46_; 
v___x_46_ = lean_unbox(v_defValue_43_);
return v___x_46_;
}
else
{
lean_object* v_val_47_; 
v_val_47_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_val_47_);
lean_dec_ref_known(v___x_45_, 1);
if (lean_obj_tag(v_val_47_) == 1)
{
uint8_t v_v_48_; 
v_v_48_ = lean_ctor_get_uint8(v_val_47_, 0);
lean_dec_ref_known(v_val_47_, 0);
return v_v_48_;
}
else
{
uint8_t v___x_49_; 
lean_dec(v_val_47_);
v___x_49_ = lean_unbox(v_defValue_43_);
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_opts_50_, lean_object* v_opt_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_opts_50_, v_opt_51_);
lean_dec_ref(v_opt_51_);
lean_dec_ref(v_opts_50_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_62_, uint8_t v___y_63_, lean_object* v_x_64_){
_start:
{
if (lean_obj_tag(v_x_64_) == 1)
{
lean_object* v_pre_65_; 
v_pre_65_ = lean_ctor_get(v_x_64_, 0);
switch(lean_obj_tag(v_pre_65_))
{
case 1:
{
lean_object* v_pre_66_; 
v_pre_66_ = lean_ctor_get(v_pre_65_, 0);
switch(lean_obj_tag(v_pre_66_))
{
case 0:
{
lean_object* v_str_67_; lean_object* v_str_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_str_67_ = lean_ctor_get(v_x_64_, 1);
v_str_68_ = lean_ctor_get(v_pre_65_, 1);
v___x_69_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__0));
v___x_70_ = lean_string_dec_eq(v_str_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__1));
v___x_72_ = lean_string_dec_eq(v_str_68_, v___x_71_);
if (v___x_72_ == 0)
{
return v___x_72_;
}
else
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__2));
v___x_74_ = lean_string_dec_eq(v_str_67_, v___x_73_);
if (v___x_74_ == 0)
{
return v___x_74_;
}
else
{
return v_suppressElabErrors_62_;
}
}
}
else
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__3));
v___x_76_ = lean_string_dec_eq(v_str_67_, v___x_75_);
if (v___x_76_ == 0)
{
return v___x_76_;
}
else
{
return v_suppressElabErrors_62_;
}
}
}
case 1:
{
lean_object* v_pre_77_; 
v_pre_77_ = lean_ctor_get(v_pre_66_, 0);
if (lean_obj_tag(v_pre_77_) == 0)
{
lean_object* v_str_78_; lean_object* v_str_79_; lean_object* v_str_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_str_78_ = lean_ctor_get(v_x_64_, 1);
v_str_79_ = lean_ctor_get(v_pre_65_, 1);
v_str_80_ = lean_ctor_get(v_pre_66_, 1);
v___x_81_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__4));
v___x_82_ = lean_string_dec_eq(v_str_80_, v___x_81_);
if (v___x_82_ == 0)
{
return v___x_82_;
}
else
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__5));
v___x_84_ = lean_string_dec_eq(v_str_79_, v___x_83_);
if (v___x_84_ == 0)
{
return v___x_84_;
}
else
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__6));
v___x_86_ = lean_string_dec_eq(v_str_78_, v___x_85_);
if (v___x_86_ == 0)
{
return v___x_86_;
}
else
{
return v_suppressElabErrors_62_;
}
}
}
}
else
{
return v___y_63_;
}
}
default: 
{
return v___y_63_;
}
}
}
case 0:
{
lean_object* v_str_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_str_87_ = lean_ctor_get(v_x_64_, 1);
v___x_88_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7));
v___x_89_ = lean_string_dec_eq(v_str_87_, v___x_88_);
if (v___x_89_ == 0)
{
return v___x_89_;
}
else
{
return v_suppressElabErrors_62_;
}
}
default: 
{
return v___y_63_;
}
}
}
else
{
return v___y_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_90_, lean_object* v___y_91_, lean_object* v_x_92_){
_start:
{
uint8_t v_suppressElabErrors_boxed_93_; uint8_t v___y_2821__boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v_suppressElabErrors_boxed_93_ = lean_unbox(v_suppressElabErrors_90_);
v___y_2821__boxed_94_ = lean_unbox(v___y_91_);
v_res_95_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_93_, v___y_2821__boxed_94_, v_x_92_);
lean_dec(v_x_92_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_ref_98_, lean_object* v_msgData_99_, uint8_t v_severity_100_, uint8_t v_isSilent_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___y_106_; uint8_t v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; uint8_t v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v_toCold_113_; lean_object* v___y_114_; lean_object* v___y_143_; lean_object* v___y_144_; uint8_t v___y_145_; uint8_t v___y_146_; lean_object* v___y_147_; uint8_t v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___y_170_; lean_object* v___y_171_; uint8_t v___y_172_; uint8_t v___y_173_; lean_object* v___y_174_; uint8_t v___y_175_; lean_object* v___y_176_; uint8_t v___y_180_; uint8_t v___y_181_; uint8_t v___y_182_; uint8_t v___x_193_; uint8_t v___y_195_; uint8_t v___y_196_; uint8_t v___y_197_; uint8_t v___y_199_; uint8_t v___x_207_; 
v___x_193_ = 2;
v___x_207_ = l_Lean_instBEqMessageSeverity_beq(v_severity_100_, v___x_193_);
if (v___x_207_ == 0)
{
v___y_199_ = v___x_207_;
goto v___jp_198_;
}
else
{
uint8_t v___x_208_; 
lean_inc_ref(v_msgData_99_);
v___x_208_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_99_);
v___y_199_ = v___x_208_;
goto v___jp_198_;
}
v___jp_105_:
{
lean_object* v_currNamespace_115_; lean_object* v_openDecls_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_env_121_; lean_object* v_nextMacroScope_122_; lean_object* v_ngen_123_; lean_object* v_auxDeclNGen_124_; lean_object* v_traceState_125_; lean_object* v_cache_126_; lean_object* v_recordedDeps_127_; lean_object* v_messages_128_; lean_object* v_infoState_129_; lean_object* v_snapshotTasks_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_141_; 
v_currNamespace_115_ = lean_ctor_get(v_toCold_113_, 4);
v_openDecls_116_ = lean_ctor_get(v_toCold_113_, 5);
lean_inc(v_openDecls_116_);
lean_inc(v_currNamespace_115_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v_currNamespace_115_);
lean_ctor_set(v___x_117_, 1, v_openDecls_116_);
v___x_118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___y_106_);
lean_inc_ref(v___y_112_);
lean_inc_ref(v___y_111_);
v___x_119_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_119_, 0, v___y_111_);
lean_ctor_set(v___x_119_, 1, v___y_109_);
lean_ctor_set(v___x_119_, 2, v___y_108_);
lean_ctor_set(v___x_119_, 3, v___y_112_);
lean_ctor_set(v___x_119_, 4, v___x_118_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*5, v___y_107_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*5 + 1, v___y_110_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*5 + 2, v_isSilent_101_);
v___x_120_ = lean_st_ref_take(v___y_114_);
v_env_121_ = lean_ctor_get(v___x_120_, 0);
v_nextMacroScope_122_ = lean_ctor_get(v___x_120_, 1);
v_ngen_123_ = lean_ctor_get(v___x_120_, 2);
v_auxDeclNGen_124_ = lean_ctor_get(v___x_120_, 3);
v_traceState_125_ = lean_ctor_get(v___x_120_, 4);
v_cache_126_ = lean_ctor_get(v___x_120_, 5);
v_recordedDeps_127_ = lean_ctor_get(v___x_120_, 6);
v_messages_128_ = lean_ctor_get(v___x_120_, 7);
v_infoState_129_ = lean_ctor_get(v___x_120_, 8);
v_snapshotTasks_130_ = lean_ctor_get(v___x_120_, 9);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_141_ == 0)
{
v___x_132_ = v___x_120_;
v_isShared_133_ = v_isSharedCheck_141_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_snapshotTasks_130_);
lean_inc(v_infoState_129_);
lean_inc(v_messages_128_);
lean_inc(v_recordedDeps_127_);
lean_inc(v_cache_126_);
lean_inc(v_traceState_125_);
lean_inc(v_auxDeclNGen_124_);
lean_inc(v_ngen_123_);
lean_inc(v_nextMacroScope_122_);
lean_inc(v_env_121_);
lean_dec(v___x_120_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_141_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_134_ = lean_box(0);
v___x_135_ = l_Lean_MessageLog_add(v___x_119_, v_messages_128_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 7, v___x_135_);
v___x_137_ = v___x_132_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_env_121_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_nextMacroScope_122_);
lean_ctor_set(v_reuseFailAlloc_140_, 2, v_ngen_123_);
lean_ctor_set(v_reuseFailAlloc_140_, 3, v_auxDeclNGen_124_);
lean_ctor_set(v_reuseFailAlloc_140_, 4, v_traceState_125_);
lean_ctor_set(v_reuseFailAlloc_140_, 5, v_cache_126_);
lean_ctor_set(v_reuseFailAlloc_140_, 6, v_recordedDeps_127_);
lean_ctor_set(v_reuseFailAlloc_140_, 7, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_140_, 8, v_infoState_129_);
lean_ctor_set(v_reuseFailAlloc_140_, 9, v_snapshotTasks_130_);
v___x_137_ = v_reuseFailAlloc_140_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_st_ref_put(v___y_114_, v___x_137_);
v___x_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_134_);
return v___x_139_;
}
}
}
v___jp_142_:
{
lean_object* v_fileName_151_; lean_object* v_fileMap_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_168_; 
v_fileName_151_ = lean_ctor_get(v___y_149_, 0);
v_fileMap_152_ = lean_ctor_get(v___y_149_, 1);
v___x_153_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_99_);
v___x_154_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(v___x_153_, v___y_102_, v___y_103_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_168_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_168_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_168_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_inc_ref_n(v_fileMap_152_, 2);
v___x_159_ = l_Lean_FileMap_toPosition(v_fileMap_152_, v___y_147_);
lean_dec(v___y_147_);
v___x_160_ = l_Lean_FileMap_toPosition(v_fileMap_152_, v___y_150_);
lean_dec(v___y_150_);
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
v___x_162_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___closed__0));
if (v___y_148_ == 0)
{
lean_del_object(v___x_157_);
lean_dec_ref(v___y_143_);
v___y_106_ = v_a_155_;
v___y_107_ = v___y_145_;
v___y_108_ = v___x_161_;
v___y_109_ = v___x_159_;
v___y_110_ = v___y_146_;
v___y_111_ = v_fileName_151_;
v___y_112_ = v___x_162_;
v_toCold_113_ = v___y_144_;
v___y_114_ = v___y_103_;
goto v___jp_105_;
}
else
{
uint8_t v___x_163_; 
lean_inc(v_a_155_);
v___x_163_ = l_Lean_MessageData_hasTag(v___y_143_, v_a_155_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec_ref_known(v___x_161_, 1);
lean_dec_ref(v___x_159_);
lean_dec(v_a_155_);
v___x_164_ = lean_box(0);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_164_);
v___x_166_ = v___x_157_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
lean_del_object(v___x_157_);
v___y_106_ = v_a_155_;
v___y_107_ = v___y_145_;
v___y_108_ = v___x_161_;
v___y_109_ = v___x_159_;
v___y_110_ = v___y_146_;
v___y_111_ = v_fileName_151_;
v___y_112_ = v___x_162_;
v_toCold_113_ = v___y_144_;
v___y_114_ = v___y_103_;
goto v___jp_105_;
}
}
}
}
v___jp_169_:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Syntax_getTailPos_x3f(v___y_174_, v___y_173_);
lean_dec(v___y_174_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_inc(v___y_176_);
v___y_143_ = v___y_170_;
v___y_144_ = v___y_171_;
v___y_145_ = v___y_173_;
v___y_146_ = v___y_175_;
v___y_147_ = v___y_176_;
v___y_148_ = v___y_172_;
v___y_149_ = v___y_171_;
v___y_150_ = v___y_176_;
goto v___jp_142_;
}
else
{
lean_object* v_val_178_; 
v_val_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_val_178_);
lean_dec_ref_known(v___x_177_, 1);
v___y_143_ = v___y_170_;
v___y_144_ = v___y_171_;
v___y_145_ = v___y_173_;
v___y_146_ = v___y_175_;
v___y_147_ = v___y_176_;
v___y_148_ = v___y_172_;
v___y_149_ = v___y_171_;
v___y_150_ = v_val_178_;
goto v___jp_142_;
}
}
v___jp_179_:
{
lean_object* v_toCold_183_; lean_object* v_ref_184_; uint8_t v_suppressElabErrors_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___f_188_; lean_object* v_ref_189_; lean_object* v___x_190_; 
v_toCold_183_ = lean_ctor_get(v___y_102_, 0);
v_ref_184_ = lean_ctor_get(v___y_102_, 2);
v_suppressElabErrors_185_ = lean_ctor_get_uint8(v___y_102_, sizeof(void*)*3 + 2);
v___x_186_ = lean_box(v_suppressElabErrors_185_);
v___x_187_ = lean_box(v___y_180_);
v___f_188_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_188_, 0, v___x_186_);
lean_closure_set(v___f_188_, 1, v___x_187_);
v_ref_189_ = l_Lean_replaceRef(v_ref_98_, v_ref_184_);
v___x_190_ = l_Lean_Syntax_getPos_x3f(v_ref_189_, v___y_181_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___y_170_ = v___f_188_;
v___y_171_ = v_toCold_183_;
v___y_172_ = v_suppressElabErrors_185_;
v___y_173_ = v___y_181_;
v___y_174_ = v_ref_189_;
v___y_175_ = v___y_182_;
v___y_176_ = v___x_191_;
goto v___jp_169_;
}
else
{
lean_object* v_val_192_; 
v_val_192_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v___x_190_, 1);
v___y_170_ = v___f_188_;
v___y_171_ = v_toCold_183_;
v___y_172_ = v_suppressElabErrors_185_;
v___y_173_ = v___y_181_;
v___y_174_ = v_ref_189_;
v___y_175_ = v___y_182_;
v___y_176_ = v_val_192_;
goto v___jp_169_;
}
}
v___jp_194_:
{
if (v___y_197_ == 0)
{
v___y_180_ = v___y_195_;
v___y_181_ = v___y_196_;
v___y_182_ = v_severity_100_;
goto v___jp_179_;
}
else
{
v___y_180_ = v___y_195_;
v___y_181_ = v___y_196_;
v___y_182_ = v___x_193_;
goto v___jp_179_;
}
}
v___jp_198_:
{
if (v___y_199_ == 0)
{
uint8_t v___x_200_; uint8_t v___x_201_; 
v___x_200_ = 1;
v___x_201_ = l_Lean_instBEqMessageSeverity_beq(v_severity_100_, v___x_200_);
if (v___x_201_ == 0)
{
v___y_195_ = v___y_199_;
v___y_196_ = v___y_199_;
v___y_197_ = v___x_201_;
goto v___jp_194_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_202_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_102_);
v___x_203_ = l_Lean_warningAsError;
v___x_204_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(v___x_202_, v___x_203_);
lean_dec_ref(v___x_202_);
v___y_195_ = v___y_199_;
v___y_196_ = v___y_199_;
v___y_197_ = v___x_204_;
goto v___jp_194_;
}
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec_ref(v_msgData_99_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_ref_209_, lean_object* v_msgData_210_, lean_object* v_severity_211_, lean_object* v_isSilent_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
uint8_t v_severity_boxed_216_; uint8_t v_isSilent_boxed_217_; lean_object* v_res_218_; 
v_severity_boxed_216_ = lean_unbox(v_severity_211_);
v_isSilent_boxed_217_ = lean_unbox(v_isSilent_212_);
v_res_218_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(v_ref_209_, v_msgData_210_, v_severity_boxed_216_, v_isSilent_boxed_217_, v___y_213_, v___y_214_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v_ref_209_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(lean_object* v_ref_219_, lean_object* v_msgData_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; 
v___x_224_ = 1;
v___x_225_ = 0;
v___x_226_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(v_ref_219_, v_msgData_220_, v___x_224_, v___x_225_, v___y_221_, v___y_222_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0___boxed(lean_object* v_ref_227_, lean_object* v_msgData_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(v_ref_227_, v_msgData_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v_ref_227_);
return v_res_232_;
}
}
static lean_object* _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
v___x_237_ = l_Lean_MessageData_ofFormat(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(lean_object* v_add_238_, lean_object* v_decl_239_, lean_object* v_stx_240_, uint8_t v_attrKind_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_, &l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_);
v___x_246_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(v_stx_240_, v___x_245_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref_known(v___x_246_, 1);
v___x_247_ = lean_box(v_attrKind_241_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
v___x_248_ = lean_apply_6(v_add_238_, v_decl_239_, v_stx_240_, v___x_247_, v___y_242_, v___y_243_, lean_box(0));
return v___x_248_;
}
else
{
lean_dec(v_stx_240_);
lean_dec(v_decl_239_);
lean_dec_ref(v_add_238_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_add_249_, lean_object* v_decl_250_, lean_object* v_stx_251_, lean_object* v_attrKind_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
uint8_t v_attrKind_boxed_256_; lean_object* v_res_257_; 
v_attrKind_boxed_256_ = lean_unbox(v_attrKind_252_);
v_res_257_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(v_add_249_, v_decl_250_, v_stx_251_, v_attrKind_boxed_256_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(lean_object* v_erase_258_, lean_object* v_decl_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; 
lean_inc(v___y_261_);
lean_inc_ref(v___y_260_);
v___x_263_ = lean_apply_4(v_erase_258_, v_decl_259_, v___y_260_, v___y_261_, lean_box(0));
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_erase_264_, lean_object* v_decl_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(v_erase_264_, v_decl_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_327_; lean_object* v_attr_328_; lean_object* v_toAttributeImplCore_329_; lean_object* v_add_330_; lean_object* v_erase_331_; lean_object* v_descr_332_; uint8_t v_applicationTime_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___f_336_; lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_327_ = l_Lake_testDriverAttr;
v_attr_328_ = lean_ctor_get(v___x_327_, 0);
v_toAttributeImplCore_329_ = lean_ctor_get(v_attr_328_, 0);
v_add_330_ = lean_ctor_get(v_attr_328_, 1);
v_erase_331_ = lean_ctor_get(v_attr_328_, 2);
v_descr_332_ = lean_ctor_get(v_toAttributeImplCore_329_, 2);
v_applicationTime_333_ = lean_ctor_get_uint8(v_toAttributeImplCore_329_, sizeof(void*)*3);
v___x_334_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
v___x_335_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
lean_inc_ref(v_add_330_);
v___f_336_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed), 7, 1);
lean_closure_set(v___f_336_, 0, v_add_330_);
lean_inc_ref(v_erase_331_);
v___f_337_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_337_, 0, v_erase_331_);
lean_inc_ref(v_descr_332_);
v___x_338_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_338_, 0, v___x_334_);
lean_ctor_set(v___x_338_, 1, v___x_335_);
lean_ctor_set(v___x_338_, 2, v_descr_332_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*3, v_applicationTime_333_);
v___x_339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___f_336_);
lean_ctor_set(v___x_339_, 2, v___f_337_);
v___x_340_ = l_Lean_registerBuiltinAttribute(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_();
return v_res_342_;
}
}
lean_object* runtime_initialize_Lake_DSL_AttributesCore(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_DSL_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_DSL_AttributesCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_DSL_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_DSL_AttributesCore(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_AttributesCore(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_DSL_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_DSL_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_DSL_Attributes(builtin);
}
#ifdef __cplusplus
}
#endif
