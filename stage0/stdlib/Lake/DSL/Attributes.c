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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1);
v___x_6_ = lean_unsigned_to_nat(0u);
v___x_7_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_5_);
lean_ctor_set(v___x_7_, 5, v___x_5_);
lean_ctor_set(v___x_7_, 6, v___x_5_);
lean_ctor_set(v___x_7_, 7, v___x_5_);
lean_ctor_set(v___x_7_, 8, v___x_5_);
lean_ctor_set(v___x_7_, 9, v___x_5_);
lean_ctor_set(v___x_7_, 10, v___x_5_);
lean_ctor_set(v___x_7_, 11, v___x_4_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_unsigned_to_nat(32u);
v___x_9_ = lean_mk_empty_array_with_capacity(v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_11_ = ((size_t)5ULL);
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_unsigned_to_nat(32u);
v___x_14_ = lean_mk_empty_array_with_capacity(v___x_13_);
v___x_15_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__3);
v___x_16_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_12_);
lean_ctor_set(v___x_16_, 3, v___x_12_);
lean_ctor_set_usize(v___x_16_, 4, v___x_11_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = lean_box(1);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__4);
v___x_19_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__1);
v___x_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_17_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_msgData_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; lean_object* v_toCold_26_; lean_object* v_env_27_; lean_object* v_options_28_; uint8_t v___x_29_; lean_object* v_env_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_25_ = lean_st_ref_get(v___y_23_);
v_toCold_26_ = lean_ctor_get(v___y_22_, 0);
v_env_27_ = lean_ctor_get(v___x_25_, 0);
lean_inc_ref(v_env_27_);
lean_dec(v___x_25_);
v_options_28_ = lean_ctor_get(v_toCold_26_, 2);
v___x_29_ = 0;
v_env_30_ = l_Lean_Environment_setRecordingDeps(v_env_27_, v___x_29_);
v___x_31_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2);
v___x_32_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_28_);
v___x_33_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_33_, 0, v_env_30_);
lean_ctor_set(v___x_33_, 1, v___x_31_);
lean_ctor_set(v___x_33_, 2, v___x_32_);
lean_ctor_set(v___x_33_, 3, v_options_28_);
v___x_34_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v_msgData_21_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_msgData_36_, v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
return v_res_40_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_opts_41_, lean_object* v_opt_42_){
_start:
{
lean_object* v_name_43_; lean_object* v_defValue_44_; lean_object* v_map_45_; lean_object* v___x_46_; 
v_name_43_ = lean_ctor_get(v_opt_42_, 0);
v_defValue_44_ = lean_ctor_get(v_opt_42_, 1);
v_map_45_ = lean_ctor_get(v_opts_41_, 0);
v___x_46_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_45_, v_name_43_);
if (lean_obj_tag(v___x_46_) == 0)
{
uint8_t v___x_47_; 
v___x_47_ = lean_unbox(v_defValue_44_);
return v___x_47_;
}
else
{
lean_object* v_val_48_; 
v_val_48_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_val_48_);
lean_dec_ref_known(v___x_46_, 1);
if (lean_obj_tag(v_val_48_) == 1)
{
uint8_t v_v_49_; 
v_v_49_ = lean_ctor_get_uint8(v_val_48_, 0);
lean_dec_ref_known(v_val_48_, 0);
return v_v_49_;
}
else
{
uint8_t v___x_50_; 
lean_dec(v_val_48_);
v___x_50_ = lean_unbox(v_defValue_44_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_opts_51_, lean_object* v_opt_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_opts_51_, v_opt_52_);
lean_dec_ref(v_opt_52_);
lean_dec_ref(v_opts_51_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_63_, lean_object* v_x_64_){
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
return v_suppressElabErrors_63_;
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
return v_suppressElabErrors_63_;
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
return v_suppressElabErrors_63_;
}
}
}
}
else
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
}
default: 
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
}
case 0:
{
lean_object* v_str_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_str_89_ = lean_ctor_get(v_x_64_, 1);
v___x_90_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7));
v___x_91_ = lean_string_dec_eq(v_str_89_, v___x_90_);
if (v___x_91_ == 0)
{
return v___x_91_;
}
else
{
return v_suppressElabErrors_63_;
}
}
default: 
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
}
else
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_94_, lean_object* v_x_95_){
_start:
{
uint8_t v_suppressElabErrors_boxed_96_; uint8_t v_res_97_; lean_object* v_r_98_; 
v_suppressElabErrors_boxed_96_ = lean_unbox(v_suppressElabErrors_94_);
v_res_97_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_96_, v_x_95_);
lean_dec(v_x_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_ref_100_, lean_object* v_msgData_101_, uint8_t v_severity_102_, uint8_t v_isSilent_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; uint8_t v___y_112_; uint8_t v___y_113_; lean_object* v___y_114_; lean_object* v_toCold_115_; lean_object* v___y_116_; lean_object* v___y_145_; lean_object* v___y_146_; uint8_t v___y_147_; uint8_t v___y_148_; uint8_t v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_172_; uint8_t v___y_173_; lean_object* v___y_174_; uint8_t v___y_175_; lean_object* v___y_176_; uint8_t v___y_177_; lean_object* v___y_178_; uint8_t v___y_182_; uint8_t v___y_183_; uint8_t v___x_193_; uint8_t v___y_195_; uint8_t v___x_201_; 
v___x_193_ = 2;
v___x_201_ = l_Lean_instBEqMessageSeverity_beq(v_severity_102_, v___x_193_);
if (v___x_201_ == 0)
{
v___y_195_ = v___x_201_;
goto v___jp_194_;
}
else
{
uint8_t v___x_202_; 
lean_inc_ref(v_msgData_101_);
v___x_202_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_101_);
if (v___x_202_ == 0)
{
v___y_195_ = v___x_202_;
goto v___jp_194_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec_ref(v_msgData_101_);
v___x_203_ = lean_box(0);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
v___jp_107_:
{
lean_object* v_currNamespace_117_; lean_object* v_openDecls_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_env_123_; lean_object* v_nextMacroScope_124_; lean_object* v_ngen_125_; lean_object* v_auxDeclNGen_126_; lean_object* v_traceState_127_; lean_object* v_cache_128_; lean_object* v_recordedDeps_129_; lean_object* v_messages_130_; lean_object* v_infoState_131_; lean_object* v_snapshotTasks_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_143_; 
v_currNamespace_117_ = lean_ctor_get(v_toCold_115_, 4);
v_openDecls_118_ = lean_ctor_get(v_toCold_115_, 5);
lean_inc(v_openDecls_118_);
lean_inc(v_currNamespace_117_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_currNamespace_117_);
lean_ctor_set(v___x_119_, 1, v_openDecls_118_);
v___x_120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___y_110_);
lean_inc_ref(v___y_108_);
lean_inc_ref(v___y_111_);
v___x_121_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_121_, 0, v___y_111_);
lean_ctor_set(v___x_121_, 1, v___y_109_);
lean_ctor_set(v___x_121_, 2, v___y_114_);
lean_ctor_set(v___x_121_, 3, v___y_108_);
lean_ctor_set(v___x_121_, 4, v___x_120_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*5, v___y_112_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*5 + 1, v___y_113_);
lean_ctor_set_uint8(v___x_121_, sizeof(void*)*5 + 2, v_isSilent_103_);
v___x_122_ = lean_st_ref_take(v___y_116_);
v_env_123_ = lean_ctor_get(v___x_122_, 0);
v_nextMacroScope_124_ = lean_ctor_get(v___x_122_, 1);
v_ngen_125_ = lean_ctor_get(v___x_122_, 2);
v_auxDeclNGen_126_ = lean_ctor_get(v___x_122_, 3);
v_traceState_127_ = lean_ctor_get(v___x_122_, 4);
v_cache_128_ = lean_ctor_get(v___x_122_, 5);
v_recordedDeps_129_ = lean_ctor_get(v___x_122_, 6);
v_messages_130_ = lean_ctor_get(v___x_122_, 7);
v_infoState_131_ = lean_ctor_get(v___x_122_, 8);
v_snapshotTasks_132_ = lean_ctor_get(v___x_122_, 9);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_143_ == 0)
{
v___x_134_ = v___x_122_;
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_snapshotTasks_132_);
lean_inc(v_infoState_131_);
lean_inc(v_messages_130_);
lean_inc(v_recordedDeps_129_);
lean_inc(v_cache_128_);
lean_inc(v_traceState_127_);
lean_inc(v_auxDeclNGen_126_);
lean_inc(v_ngen_125_);
lean_inc(v_nextMacroScope_124_);
lean_inc(v_env_123_);
lean_dec(v___x_122_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_136_ = lean_box(0);
v___x_137_ = l_Lean_MessageLog_add(v___x_121_, v_messages_130_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 7, v___x_137_);
v___x_139_ = v___x_134_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_env_123_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_nextMacroScope_124_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_ngen_125_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_auxDeclNGen_126_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v_traceState_127_);
lean_ctor_set(v_reuseFailAlloc_142_, 5, v_cache_128_);
lean_ctor_set(v_reuseFailAlloc_142_, 6, v_recordedDeps_129_);
lean_ctor_set(v_reuseFailAlloc_142_, 7, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_142_, 8, v_infoState_131_);
lean_ctor_set(v_reuseFailAlloc_142_, 9, v_snapshotTasks_132_);
v___x_139_ = v_reuseFailAlloc_142_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_st_ref_put(v___y_116_, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_136_);
return v___x_141_;
}
}
}
v___jp_144_:
{
lean_object* v_fileName_153_; lean_object* v_fileMap_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_170_; 
v_fileName_153_ = lean_ctor_get(v___y_150_, 0);
v_fileMap_154_ = lean_ctor_get(v___y_150_, 1);
v___x_155_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_101_);
v___x_156_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(v___x_155_, v___y_104_, v___y_105_);
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_170_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_170_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_170_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_inc_ref_n(v_fileMap_154_, 2);
v___x_161_ = l_Lean_FileMap_toPosition(v_fileMap_154_, v___y_151_);
lean_dec(v___y_151_);
v___x_162_ = l_Lean_FileMap_toPosition(v_fileMap_154_, v___y_152_);
lean_dec(v___y_152_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
v___x_164_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___closed__0));
if (v___y_147_ == 0)
{
lean_del_object(v___x_159_);
lean_dec_ref(v___y_145_);
v___y_108_ = v___x_164_;
v___y_109_ = v___x_161_;
v___y_110_ = v_a_157_;
v___y_111_ = v_fileName_153_;
v___y_112_ = v___y_148_;
v___y_113_ = v___y_149_;
v___y_114_ = v___x_163_;
v_toCold_115_ = v___y_146_;
v___y_116_ = v___y_105_;
goto v___jp_107_;
}
else
{
uint8_t v___x_165_; 
lean_inc(v_a_157_);
v___x_165_ = l_Lean_MessageData_hasTag(v___y_145_, v_a_157_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_168_; 
lean_dec_ref_known(v___x_163_, 1);
lean_dec_ref(v___x_161_);
lean_dec(v_a_157_);
v___x_166_ = lean_box(0);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_166_);
v___x_168_ = v___x_159_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
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
lean_del_object(v___x_159_);
v___y_108_ = v___x_164_;
v___y_109_ = v___x_161_;
v___y_110_ = v_a_157_;
v___y_111_ = v_fileName_153_;
v___y_112_ = v___y_148_;
v___y_113_ = v___y_149_;
v___y_114_ = v___x_163_;
v_toCold_115_ = v___y_146_;
v___y_116_ = v___y_105_;
goto v___jp_107_;
}
}
}
}
v___jp_171_:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Syntax_getTailPos_x3f(v___y_176_, v___y_175_);
lean_dec(v___y_176_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_inc(v___y_178_);
v___y_145_ = v___y_172_;
v___y_146_ = v___y_174_;
v___y_147_ = v___y_173_;
v___y_148_ = v___y_175_;
v___y_149_ = v___y_177_;
v___y_150_ = v___y_174_;
v___y_151_ = v___y_178_;
v___y_152_ = v___y_178_;
goto v___jp_144_;
}
else
{
lean_object* v_val_180_; 
v_val_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v___x_179_, 1);
v___y_145_ = v___y_172_;
v___y_146_ = v___y_174_;
v___y_147_ = v___y_173_;
v___y_148_ = v___y_175_;
v___y_149_ = v___y_177_;
v___y_150_ = v___y_174_;
v___y_151_ = v___y_178_;
v___y_152_ = v_val_180_;
goto v___jp_144_;
}
}
v___jp_181_:
{
lean_object* v_toCold_184_; lean_object* v_ref_185_; uint8_t v_suppressElabErrors_186_; lean_object* v___x_187_; lean_object* v___f_188_; lean_object* v_ref_189_; lean_object* v___x_190_; 
v_toCold_184_ = lean_ctor_get(v___y_104_, 0);
v_ref_185_ = lean_ctor_get(v___y_104_, 2);
v_suppressElabErrors_186_ = lean_ctor_get_uint8(v___y_104_, sizeof(void*)*3 + 2);
v___x_187_ = lean_box(v_suppressElabErrors_186_);
v___f_188_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_188_, 0, v___x_187_);
v_ref_189_ = l_Lean_replaceRef(v_ref_100_, v_ref_185_);
v___x_190_ = l_Lean_Syntax_getPos_x3f(v_ref_189_, v___y_182_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___y_172_ = v___f_188_;
v___y_173_ = v_suppressElabErrors_186_;
v___y_174_ = v_toCold_184_;
v___y_175_ = v___y_182_;
v___y_176_ = v_ref_189_;
v___y_177_ = v___y_183_;
v___y_178_ = v___x_191_;
goto v___jp_171_;
}
else
{
lean_object* v_val_192_; 
v_val_192_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v___x_190_, 1);
v___y_172_ = v___f_188_;
v___y_173_ = v_suppressElabErrors_186_;
v___y_174_ = v_toCold_184_;
v___y_175_ = v___y_182_;
v___y_176_ = v_ref_189_;
v___y_177_ = v___y_183_;
v___y_178_ = v_val_192_;
goto v___jp_171_;
}
}
v___jp_194_:
{
uint8_t v___x_196_; uint8_t v___x_197_; 
v___x_196_ = 1;
v___x_197_ = l_Lean_instBEqMessageSeverity_beq(v_severity_102_, v___x_196_);
if (v___x_197_ == 0)
{
v___y_182_ = v___y_195_;
v___y_183_ = v_severity_102_;
goto v___jp_181_;
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_198_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_104_);
v___x_199_ = l_Lean_warningAsError;
v___x_200_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(v___x_198_, v___x_199_);
lean_dec_ref(v___x_198_);
if (v___x_200_ == 0)
{
v___y_182_ = v___y_195_;
v___y_183_ = v_severity_102_;
goto v___jp_181_;
}
else
{
v___y_182_ = v___y_195_;
v___y_183_ = v___x_193_;
goto v___jp_181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_ref_205_, lean_object* v_msgData_206_, lean_object* v_severity_207_, lean_object* v_isSilent_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
uint8_t v_severity_boxed_212_; uint8_t v_isSilent_boxed_213_; lean_object* v_res_214_; 
v_severity_boxed_212_ = lean_unbox(v_severity_207_);
v_isSilent_boxed_213_ = lean_unbox(v_isSilent_208_);
v_res_214_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(v_ref_205_, v_msgData_206_, v_severity_boxed_212_, v_isSilent_boxed_213_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v_ref_205_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(lean_object* v_ref_215_, lean_object* v_msgData_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
uint8_t v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; 
v___x_220_ = 1;
v___x_221_ = 0;
v___x_222_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(v_ref_215_, v_msgData_216_, v___x_220_, v___x_221_, v___y_217_, v___y_218_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0___boxed(lean_object* v_ref_223_, lean_object* v_msgData_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(v_ref_223_, v_msgData_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v_ref_223_);
return v_res_228_;
}
}
static lean_object* _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
v___x_233_ = l_Lean_MessageData_ofFormat(v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(lean_object* v_add_234_, lean_object* v_decl_235_, lean_object* v_stx_236_, uint8_t v_attrKind_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_obj_once(&l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_, &l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_);
v___x_242_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(v_stx_236_, v___x_241_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref_known(v___x_242_, 1);
v___x_243_ = lean_box(v_attrKind_237_);
lean_inc(v___y_239_);
lean_inc_ref(v___y_238_);
v___x_244_ = lean_apply_6(v_add_234_, v_decl_235_, v_stx_236_, v___x_243_, v___y_238_, v___y_239_, lean_box(0));
return v___x_244_;
}
else
{
lean_dec(v_stx_236_);
lean_dec(v_decl_235_);
lean_dec_ref(v_add_234_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_add_245_, lean_object* v_decl_246_, lean_object* v_stx_247_, lean_object* v_attrKind_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
uint8_t v_attrKind_boxed_252_; lean_object* v_res_253_; 
v_attrKind_boxed_252_ = lean_unbox(v_attrKind_248_);
v_res_253_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(v_add_245_, v_decl_246_, v_stx_247_, v_attrKind_boxed_252_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(lean_object* v_erase_254_, lean_object* v_decl_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; 
lean_inc(v___y_257_);
lean_inc_ref(v___y_256_);
v___x_259_ = lean_apply_4(v_erase_254_, v_decl_255_, v___y_256_, v___y_257_, lean_box(0));
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_erase_260_, lean_object* v_decl_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(v_erase_260_, v_decl_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_323_; lean_object* v_attr_324_; lean_object* v_toAttributeImplCore_325_; lean_object* v_add_326_; lean_object* v_erase_327_; lean_object* v_descr_328_; uint8_t v_applicationTime_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___f_332_; lean_object* v___f_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_323_ = l_Lake_testDriverAttr;
v_attr_324_ = lean_ctor_get(v___x_323_, 0);
v_toAttributeImplCore_325_ = lean_ctor_get(v_attr_324_, 0);
v_add_326_ = lean_ctor_get(v_attr_324_, 1);
v_erase_327_ = lean_ctor_get(v_attr_324_, 2);
v_descr_328_ = lean_ctor_get(v_toAttributeImplCore_325_, 2);
v_applicationTime_329_ = lean_ctor_get_uint8(v_toAttributeImplCore_325_, sizeof(void*)*3);
v___x_330_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
v___x_331_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
lean_inc_ref(v_add_326_);
v___f_332_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed), 7, 1);
lean_closure_set(v___f_332_, 0, v_add_326_);
lean_inc_ref(v_erase_327_);
v___f_333_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_333_, 0, v_erase_327_);
lean_inc_ref(v_descr_328_);
v___x_334_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_334_, 0, v___x_330_);
lean_ctor_set(v___x_334_, 1, v___x_331_);
lean_ctor_set(v___x_334_, 2, v_descr_328_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*3, v_applicationTime_329_);
v___x_335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___f_332_);
lean_ctor_set(v___x_335_, 2, v___f_333_);
v___x_336_ = l_Lean_registerBuiltinAttribute(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_();
return v_res_338_;
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
