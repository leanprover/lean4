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
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_msgData_21_, lean_object* v___y_22_, lean_object* v___y_23_){
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
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_21_ = stack[0].m_obj;
lean_object* v___y_22_ = stack[1].m_obj;
lean_object* v___y_23_ = stack[2].m_obj;
lean_object* v_res_36_;
v_res_36_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_msgData_21_, v___y_22_, v___y_23_);
stack->m_obj
 = v_res_36_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_msgData_37_, v___y_38_, v___y_39_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_41_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_opts_42_, lean_object* v_opt_43_){
_start:
{
lean_object* v_name_44_; lean_object* v_defValue_45_; lean_object* v_map_46_; lean_object* v___x_47_; 
v_name_44_ = lean_ctor_get(v_opt_43_, 0);
v_defValue_45_ = lean_ctor_get(v_opt_43_, 1);
v_map_46_ = lean_ctor_get(v_opts_42_, 0);
v___x_47_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_46_, v_name_44_);
if (lean_obj_tag(v___x_47_) == 0)
{
uint8_t v___x_48_; 
v___x_48_ = lean_unbox(v_defValue_45_);
return v___x_48_;
}
else
{
lean_object* v_val_49_; 
v_val_49_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_val_49_);
lean_dec_ref_known(v___x_47_, 1);
if (lean_obj_tag(v_val_49_) == 1)
{
uint8_t v_v_50_; 
v_v_50_ = lean_ctor_get_uint8(v_val_49_, 0);
lean_dec_ref_known(v_val_49_, 0);
return v_v_50_;
}
else
{
uint8_t v___x_51_; 
lean_dec(v_val_49_);
v___x_51_ = lean_unbox(v_defValue_45_);
return v___x_51_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_42_ = stack[0].m_obj;
lean_object* v_opt_43_ = stack[1].m_obj;
uint8_t v_res_52_;
v_res_52_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_opts_42_, v_opt_43_);
stack->m_num = v_res_52_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_opts_53_, lean_object* v_opt_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_opts_53_, v_opt_54_);
lean_dec_ref(v_opt_54_);
lean_dec_ref(v_opts_53_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_65_, uint8_t v___y_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_67_) == 1)
{
lean_object* v_pre_68_; 
v_pre_68_ = lean_ctor_get(v_x_67_, 0);
switch(lean_obj_tag(v_pre_68_))
{
case 1:
{
lean_object* v_pre_69_; 
v_pre_69_ = lean_ctor_get(v_pre_68_, 0);
switch(lean_obj_tag(v_pre_69_))
{
case 0:
{
lean_object* v_str_70_; lean_object* v_str_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_str_70_ = lean_ctor_get(v_x_67_, 1);
v_str_71_ = lean_ctor_get(v_pre_68_, 1);
v___x_72_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__0));
v___x_73_ = lean_string_dec_eq(v_str_71_, v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__1));
v___x_75_ = lean_string_dec_eq(v_str_71_, v___x_74_);
if (v___x_75_ == 0)
{
return v___x_75_;
}
else
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__2));
v___x_77_ = lean_string_dec_eq(v_str_70_, v___x_76_);
if (v___x_77_ == 0)
{
return v___x_77_;
}
else
{
return v_suppressElabErrors_65_;
}
}
}
else
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__3));
v___x_79_ = lean_string_dec_eq(v_str_70_, v___x_78_);
if (v___x_79_ == 0)
{
return v___x_79_;
}
else
{
return v_suppressElabErrors_65_;
}
}
}
case 1:
{
lean_object* v_pre_80_; 
v_pre_80_ = lean_ctor_get(v_pre_69_, 0);
if (lean_obj_tag(v_pre_80_) == 0)
{
lean_object* v_str_81_; lean_object* v_str_82_; lean_object* v_str_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_str_81_ = lean_ctor_get(v_x_67_, 1);
v_str_82_ = lean_ctor_get(v_pre_68_, 1);
v_str_83_ = lean_ctor_get(v_pre_69_, 1);
v___x_84_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__4));
v___x_85_ = lean_string_dec_eq(v_str_83_, v___x_84_);
if (v___x_85_ == 0)
{
return v___x_85_;
}
else
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__5));
v___x_87_ = lean_string_dec_eq(v_str_82_, v___x_86_);
if (v___x_87_ == 0)
{
return v___x_87_;
}
else
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__6));
v___x_89_ = lean_string_dec_eq(v_str_81_, v___x_88_);
if (v___x_89_ == 0)
{
return v___x_89_;
}
else
{
return v_suppressElabErrors_65_;
}
}
}
}
else
{
return v___y_66_;
}
}
default: 
{
return v___y_66_;
}
}
}
case 0:
{
lean_object* v_str_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_str_90_ = lean_ctor_get(v_x_67_, 1);
v___x_91_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7));
v___x_92_ = lean_string_dec_eq(v_str_90_, v___x_91_);
if (v___x_92_ == 0)
{
return v___x_92_;
}
else
{
return v_suppressElabErrors_65_;
}
}
default: 
{
return v___y_66_;
}
}
}
else
{
return v___y_66_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_65_ = stack[0].m_num;
uint8_t v___y_66_ = stack[1].m_num;
lean_object* v_x_67_ = stack[2].m_obj;
uint8_t v_res_93_;
v_res_93_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(v_suppressElabErrors_65_, v___y_66_, v_x_67_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_94_, lean_object* v___y_95_, lean_object* v_x_96_){
_start:
{
uint8_t v_suppressElabErrors_boxed_97_; uint8_t v___y_2868__boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_suppressElabErrors_boxed_97_ = lean_unbox(v_suppressElabErrors_94_);
v___y_2868__boxed_98_ = lean_unbox(v___y_95_);
v_res_99_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_97_, v___y_2868__boxed_98_, v_x_96_);
lean_dec(v_x_96_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_ref_102_, lean_object* v_msgData_103_, uint8_t v_severity_104_, uint8_t v_isSilent_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___y_110_; uint8_t v___y_111_; lean_object* v___y_112_; lean_object* v___y_113_; lean_object* v___y_114_; uint8_t v___y_115_; lean_object* v___y_116_; lean_object* v_toCold_117_; lean_object* v___y_118_; lean_object* v___y_147_; lean_object* v___y_148_; uint8_t v___y_149_; uint8_t v___y_150_; uint8_t v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_174_; uint8_t v___y_175_; lean_object* v___y_176_; uint8_t v___y_177_; lean_object* v___y_178_; uint8_t v___y_179_; lean_object* v___y_180_; uint8_t v___y_184_; uint8_t v___y_185_; uint8_t v___y_186_; uint8_t v___x_197_; uint8_t v___y_199_; uint8_t v___y_200_; uint8_t v___y_201_; uint8_t v___y_203_; uint8_t v___x_211_; 
v___x_197_ = 2;
v___x_211_ = l_Lean_instBEqMessageSeverity_beq(v_severity_104_, v___x_197_);
if (v___x_211_ == 0)
{
v___y_203_ = v___x_211_;
goto v___jp_202_;
}
else
{
uint8_t v___x_212_; 
lean_inc_ref(v_msgData_103_);
v___x_212_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_103_);
v___y_203_ = v___x_212_;
goto v___jp_202_;
}
v___jp_109_:
{
lean_object* v_currNamespace_119_; lean_object* v_openDecls_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_env_125_; lean_object* v_nextMacroScope_126_; lean_object* v_ngen_127_; lean_object* v_auxDeclNGen_128_; lean_object* v_traceState_129_; lean_object* v_cache_130_; lean_object* v_recordedDeps_131_; lean_object* v_messages_132_; lean_object* v_infoState_133_; lean_object* v_snapshotTasks_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_145_; 
v_currNamespace_119_ = lean_ctor_get(v_toCold_117_, 4);
v_openDecls_120_ = lean_ctor_get(v_toCold_117_, 5);
lean_inc(v_openDecls_120_);
lean_inc(v_currNamespace_119_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_currNamespace_119_);
lean_ctor_set(v___x_121_, 1, v_openDecls_120_);
v___x_122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___y_110_);
lean_inc_ref(v___y_116_);
lean_inc_ref(v___y_113_);
v___x_123_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_123_, 0, v___y_113_);
lean_ctor_set(v___x_123_, 1, v___y_114_);
lean_ctor_set(v___x_123_, 2, v___y_112_);
lean_ctor_set(v___x_123_, 3, v___y_116_);
lean_ctor_set(v___x_123_, 4, v___x_122_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*5, v___y_111_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*5 + 1, v___y_115_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*5 + 2, v_isSilent_105_);
v___x_124_ = lean_st_ref_take(v___y_118_);
v_env_125_ = lean_ctor_get(v___x_124_, 0);
v_nextMacroScope_126_ = lean_ctor_get(v___x_124_, 1);
v_ngen_127_ = lean_ctor_get(v___x_124_, 2);
v_auxDeclNGen_128_ = lean_ctor_get(v___x_124_, 3);
v_traceState_129_ = lean_ctor_get(v___x_124_, 4);
v_cache_130_ = lean_ctor_get(v___x_124_, 5);
v_recordedDeps_131_ = lean_ctor_get(v___x_124_, 6);
v_messages_132_ = lean_ctor_get(v___x_124_, 7);
v_infoState_133_ = lean_ctor_get(v___x_124_, 8);
v_snapshotTasks_134_ = lean_ctor_get(v___x_124_, 9);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_145_ == 0)
{
v___x_136_ = v___x_124_;
v_isShared_137_ = v_isSharedCheck_145_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_snapshotTasks_134_);
lean_inc(v_infoState_133_);
lean_inc(v_messages_132_);
lean_inc(v_recordedDeps_131_);
lean_inc(v_cache_130_);
lean_inc(v_traceState_129_);
lean_inc(v_auxDeclNGen_128_);
lean_inc(v_ngen_127_);
lean_inc(v_nextMacroScope_126_);
lean_inc(v_env_125_);
lean_dec(v___x_124_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_145_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_138_ = lean_box(0);
v___x_139_ = l_Lean_MessageLog_add(v___x_123_, v_messages_132_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 7, v___x_139_);
v___x_141_ = v___x_136_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_env_125_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_nextMacroScope_126_);
lean_ctor_set(v_reuseFailAlloc_144_, 2, v_ngen_127_);
lean_ctor_set(v_reuseFailAlloc_144_, 3, v_auxDeclNGen_128_);
lean_ctor_set(v_reuseFailAlloc_144_, 4, v_traceState_129_);
lean_ctor_set(v_reuseFailAlloc_144_, 5, v_cache_130_);
lean_ctor_set(v_reuseFailAlloc_144_, 6, v_recordedDeps_131_);
lean_ctor_set(v_reuseFailAlloc_144_, 7, v___x_139_);
lean_ctor_set(v_reuseFailAlloc_144_, 8, v_infoState_133_);
lean_ctor_set(v_reuseFailAlloc_144_, 9, v_snapshotTasks_134_);
v___x_141_ = v_reuseFailAlloc_144_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_st_ref_put(v___y_118_, v___x_141_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_138_);
return v___x_143_;
}
}
}
v___jp_146_:
{
lean_object* v_fileName_155_; lean_object* v_fileMap_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_172_; 
v_fileName_155_ = lean_ctor_get(v___y_152_, 0);
v_fileMap_156_ = lean_ctor_get(v___y_152_, 1);
v___x_157_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_103_);
v___x_158_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(v___x_157_, v___y_106_, v___y_107_);
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_172_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_172_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_172_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
lean_inc_ref_n(v_fileMap_156_, 2);
v___x_163_ = l_Lean_FileMap_toPosition(v_fileMap_156_, v___y_153_);
lean_dec(v___y_153_);
v___x_164_ = l_Lean_FileMap_toPosition(v_fileMap_156_, v___y_154_);
lean_dec(v___y_154_);
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___x_166_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___closed__0));
if (v___y_149_ == 0)
{
lean_del_object(v___x_161_);
lean_dec_ref(v___y_147_);
v___y_110_ = v_a_159_;
v___y_111_ = v___y_150_;
v___y_112_ = v___x_165_;
v___y_113_ = v_fileName_155_;
v___y_114_ = v___x_163_;
v___y_115_ = v___y_151_;
v___y_116_ = v___x_166_;
v_toCold_117_ = v___y_148_;
v___y_118_ = v___y_107_;
goto v___jp_109_;
}
else
{
uint8_t v___x_167_; 
lean_inc(v_a_159_);
v___x_167_ = l_Lean_MessageData_hasTag(v___y_147_, v_a_159_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_dec_ref_known(v___x_165_, 1);
lean_dec_ref(v___x_163_);
lean_dec(v_a_159_);
v___x_168_ = lean_box(0);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_168_);
v___x_170_ = v___x_161_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
else
{
lean_del_object(v___x_161_);
v___y_110_ = v_a_159_;
v___y_111_ = v___y_150_;
v___y_112_ = v___x_165_;
v___y_113_ = v_fileName_155_;
v___y_114_ = v___x_163_;
v___y_115_ = v___y_151_;
v___y_116_ = v___x_166_;
v_toCold_117_ = v___y_148_;
v___y_118_ = v___y_107_;
goto v___jp_109_;
}
}
}
}
v___jp_173_:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Syntax_getTailPos_x3f(v___y_178_, v___y_177_);
lean_dec(v___y_178_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_inc(v___y_180_);
v___y_147_ = v___y_174_;
v___y_148_ = v___y_176_;
v___y_149_ = v___y_175_;
v___y_150_ = v___y_177_;
v___y_151_ = v___y_179_;
v___y_152_ = v___y_176_;
v___y_153_ = v___y_180_;
v___y_154_ = v___y_180_;
goto v___jp_146_;
}
else
{
lean_object* v_val_182_; 
v_val_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_val_182_);
lean_dec_ref_known(v___x_181_, 1);
v___y_147_ = v___y_174_;
v___y_148_ = v___y_176_;
v___y_149_ = v___y_175_;
v___y_150_ = v___y_177_;
v___y_151_ = v___y_179_;
v___y_152_ = v___y_176_;
v___y_153_ = v___y_180_;
v___y_154_ = v_val_182_;
goto v___jp_146_;
}
}
v___jp_183_:
{
lean_object* v_toCold_187_; lean_object* v_ref_188_; uint8_t v_suppressElabErrors_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___f_192_; lean_object* v_ref_193_; lean_object* v___x_194_; 
v_toCold_187_ = lean_ctor_get(v___y_106_, 0);
v_ref_188_ = lean_ctor_get(v___y_106_, 2);
v_suppressElabErrors_189_ = lean_ctor_get_uint8(v___y_106_, sizeof(void*)*3 + 2);
v___x_190_ = lean_box(v_suppressElabErrors_189_);
v___x_191_ = lean_box(v___y_184_);
v___f_192_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_192_, 0, v___x_190_);
lean_closure_set(v___f_192_, 1, v___x_191_);
v_ref_193_ = l_Lean_replaceRef(v_ref_102_, v_ref_188_);
v___x_194_ = l_Lean_Syntax_getPos_x3f(v_ref_193_, v___y_185_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_unsigned_to_nat(0u);
v___y_174_ = v___f_192_;
v___y_175_ = v_suppressElabErrors_189_;
v___y_176_ = v_toCold_187_;
v___y_177_ = v___y_185_;
v___y_178_ = v_ref_193_;
v___y_179_ = v___y_186_;
v___y_180_ = v___x_195_;
goto v___jp_173_;
}
else
{
lean_object* v_val_196_; 
v_val_196_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v___x_194_, 1);
v___y_174_ = v___f_192_;
v___y_175_ = v_suppressElabErrors_189_;
v___y_176_ = v_toCold_187_;
v___y_177_ = v___y_185_;
v___y_178_ = v_ref_193_;
v___y_179_ = v___y_186_;
v___y_180_ = v_val_196_;
goto v___jp_173_;
}
}
v___jp_198_:
{
if (v___y_201_ == 0)
{
v___y_184_ = v___y_199_;
v___y_185_ = v___y_200_;
v___y_186_ = v_severity_104_;
goto v___jp_183_;
}
else
{
v___y_184_ = v___y_199_;
v___y_185_ = v___y_200_;
v___y_186_ = v___x_197_;
goto v___jp_183_;
}
}
v___jp_202_:
{
if (v___y_203_ == 0)
{
uint8_t v___x_204_; uint8_t v___x_205_; 
v___x_204_ = 1;
v___x_205_ = l_Lean_instBEqMessageSeverity_beq(v_severity_104_, v___x_204_);
if (v___x_205_ == 0)
{
v___y_199_ = v___y_203_;
v___y_200_ = v___y_203_;
v___y_201_ = v___x_205_;
goto v___jp_198_;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_206_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_106_);
v___x_207_ = l_Lean_warningAsError;
v___x_208_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(v___x_206_, v___x_207_);
lean_dec_ref(v___x_206_);
v___y_199_ = v___y_203_;
v___y_200_ = v___y_203_;
v___y_201_ = v___x_208_;
goto v___jp_198_;
}
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_dec_ref(v_msgData_103_);
v___x_209_ = lean_box(0);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_102_ = stack[0].m_obj;
lean_object* v_msgData_103_ = stack[1].m_obj;
uint8_t v_severity_104_ = stack[2].m_num;
uint8_t v_isSilent_105_ = stack[3].m_num;
lean_object* v___y_106_ = stack[4].m_obj;
lean_object* v___y_107_ = stack[5].m_obj;
lean_object* v_res_213_;
v_res_213_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(v_ref_102_, v_msgData_103_, v_severity_104_, v_isSilent_105_, v___y_106_, v___y_107_);
stack->m_obj
 = v_res_213_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_ref_214_, lean_object* v_msgData_215_, lean_object* v_severity_216_, lean_object* v_isSilent_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
uint8_t v_severity_boxed_221_; uint8_t v_isSilent_boxed_222_; lean_object* v_res_223_; 
v_severity_boxed_221_ = lean_unbox(v_severity_216_);
v_isSilent_boxed_222_ = lean_unbox(v_isSilent_217_);
v_res_223_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(v_ref_214_, v_msgData_215_, v_severity_boxed_221_, v_isSilent_boxed_222_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v_ref_214_);
return v_res_223_;
}
}
lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(lean_object* v_ref_224_, lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
uint8_t v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; 
v___x_229_ = 1;
v___x_230_ = 0;
v___x_231_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(v_ref_224_, v_msgData_225_, v___x_229_, v___x_230_, v___y_226_, v___y_227_);
return v___x_231_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_224_ = stack[0].m_obj;
lean_object* v_msgData_225_ = stack[1].m_obj;
lean_object* v___y_226_ = stack[2].m_obj;
lean_object* v___y_227_ = stack[3].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(v_ref_224_, v_msgData_225_, v___y_226_, v___y_227_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0___boxed(lean_object* v_ref_233_, lean_object* v_msgData_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(v_ref_233_, v_msgData_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v_ref_233_);
return v_res_238_;
}
}
static lean_object* _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
v___x_243_ = l_Lean_MessageData_ofFormat(v___x_242_);
return v___x_243_;
}
}
lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(lean_object* v_add_244_, lean_object* v_decl_245_, lean_object* v_stx_246_, uint8_t v_attrKind_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_obj_once(&l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_, &l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_);
v___x_252_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(v_stx_246_, v___x_251_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref_known(v___x_252_, 1);
v___x_253_ = lean_box(v_attrKind_247_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
v___x_254_ = lean_apply_6(v_add_244_, v_decl_245_, v_stx_246_, v___x_253_, v___y_248_, v___y_249_, lean_box(0));
return v___x_254_;
}
else
{
lean_dec(v_stx_246_);
lean_dec(v_decl_245_);
lean_dec_ref(v_add_244_);
return v___x_252_;
}
}
}
LEAN_EXPORT void l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_add_244_ = stack[0].m_obj;
lean_object* v_decl_245_ = stack[1].m_obj;
lean_object* v_stx_246_ = stack[2].m_obj;
uint8_t v_attrKind_247_ = stack[3].m_num;
lean_object* v___y_248_ = stack[4].m_obj;
lean_object* v___y_249_ = stack[5].m_obj;
lean_object* v_res_255_;
v_res_255_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(v_add_244_, v_decl_245_, v_stx_246_, v_attrKind_247_, v___y_248_, v___y_249_);
stack->m_obj
 = v_res_255_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_add_256_, lean_object* v_decl_257_, lean_object* v_stx_258_, lean_object* v_attrKind_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
uint8_t v_attrKind_boxed_263_; lean_object* v_res_264_; 
v_attrKind_boxed_263_ = lean_unbox(v_attrKind_259_);
v_res_264_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(v_add_256_, v_decl_257_, v_stx_258_, v_attrKind_boxed_263_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
return v_res_264_;
}
}
lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(lean_object* v_erase_265_, lean_object* v_decl_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; 
lean_inc(v___y_268_);
lean_inc_ref(v___y_267_);
v___x_270_ = lean_apply_4(v_erase_265_, v_decl_266_, v___y_267_, v___y_268_, lean_box(0));
return v___x_270_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_erase_265_ = stack[0].m_obj;
lean_object* v_decl_266_ = stack[1].m_obj;
lean_object* v___y_267_ = stack[2].m_obj;
lean_object* v___y_268_ = stack[3].m_obj;
lean_object* v_res_271_;
v_res_271_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(v_erase_265_, v_decl_266_, v___y_267_, v___y_268_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_erase_272_, lean_object* v_decl_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(v_erase_272_, v_decl_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_277_;
}
}
lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_335_; lean_object* v_attr_336_; lean_object* v_toAttributeImplCore_337_; lean_object* v_add_338_; lean_object* v_erase_339_; lean_object* v_descr_340_; uint8_t v_applicationTime_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___f_344_; lean_object* v___f_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_335_ = l_Lake_testDriverAttr;
v_attr_336_ = lean_ctor_get(v___x_335_, 0);
v_toAttributeImplCore_337_ = lean_ctor_get(v_attr_336_, 0);
v_add_338_ = lean_ctor_get(v_attr_336_, 1);
v_erase_339_ = lean_ctor_get(v_attr_336_, 2);
v_descr_340_ = lean_ctor_get(v_toAttributeImplCore_337_, 2);
v_applicationTime_341_ = lean_ctor_get_uint8(v_toAttributeImplCore_337_, sizeof(void*)*3);
v___x_342_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
v___x_343_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
lean_inc_ref(v_add_338_);
v___f_344_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed), 7, 1);
lean_closure_set(v___f_344_, 0, v_add_338_);
lean_inc_ref(v_erase_339_);
v___f_345_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_345_, 0, v_erase_339_);
lean_inc_ref(v_descr_340_);
v___x_346_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_346_, 0, v___x_342_);
lean_ctor_set(v___x_346_, 1, v___x_343_);
lean_ctor_set(v___x_346_, 2, v_descr_340_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*3, v_applicationTime_341_);
v___x_347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___f_344_);
lean_ctor_set(v___x_347_, 2, v___f_345_);
v___x_348_ = l_Lean_registerBuiltinAttribute(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT void l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_349_;
v_res_349_ = l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_();
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_();
return v_res_351_;
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
