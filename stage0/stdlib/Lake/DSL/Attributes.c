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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_24_; lean_object* v_toCold_25_; lean_object* v_env_26_; lean_object* v_options_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_toCold_25_ = lean_ctor_get(v___y_21_, 0);
v_env_26_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_24_);
v_options_27_ = lean_ctor_get(v_toCold_25_, 2);
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__2);
v___x_29_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_27_);
v___x_30_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_30_, 0, v_env_26_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
lean_ctor_set(v___x_30_, 3, v_options_27_);
v___x_31_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v_msgData_20_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_msgData_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_37_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_opts_38_, lean_object* v_opt_39_){
_start:
{
lean_object* v_name_40_; lean_object* v_defValue_41_; lean_object* v_map_42_; lean_object* v___x_43_; 
v_name_40_ = lean_ctor_get(v_opt_39_, 0);
v_defValue_41_ = lean_ctor_get(v_opt_39_, 1);
v_map_42_ = lean_ctor_get(v_opts_38_, 0);
v___x_43_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_42_, v_name_40_);
if (lean_obj_tag(v___x_43_) == 0)
{
uint8_t v___x_44_; 
v___x_44_ = lean_unbox(v_defValue_41_);
return v___x_44_;
}
else
{
lean_object* v_val_45_; 
v_val_45_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v___x_43_, 1);
if (lean_obj_tag(v_val_45_) == 1)
{
uint8_t v_v_46_; 
v_v_46_ = lean_ctor_get_uint8(v_val_45_, 0);
lean_dec_ref_known(v_val_45_, 0);
return v_v_46_;
}
else
{
uint8_t v___x_47_; 
lean_dec(v_val_45_);
v___x_47_ = lean_unbox(v_defValue_41_);
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_opts_48_, lean_object* v_opt_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_opts_48_, v_opt_49_);
lean_dec_ref(v_opt_49_);
lean_dec_ref(v_opts_48_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_60_, uint8_t v___y_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_62_) == 1)
{
lean_object* v_pre_63_; 
v_pre_63_ = lean_ctor_get(v_x_62_, 0);
switch(lean_obj_tag(v_pre_63_))
{
case 1:
{
lean_object* v_pre_64_; 
v_pre_64_ = lean_ctor_get(v_pre_63_, 0);
switch(lean_obj_tag(v_pre_64_))
{
case 0:
{
lean_object* v_str_65_; lean_object* v_str_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_str_65_ = lean_ctor_get(v_x_62_, 1);
v_str_66_ = lean_ctor_get(v_pre_63_, 1);
v___x_67_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__0));
v___x_68_ = lean_string_dec_eq(v_str_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__1));
v___x_70_ = lean_string_dec_eq(v_str_66_, v___x_69_);
if (v___x_70_ == 0)
{
return v___x_70_;
}
else
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__2));
v___x_72_ = lean_string_dec_eq(v_str_65_, v___x_71_);
if (v___x_72_ == 0)
{
return v___x_72_;
}
else
{
return v_suppressElabErrors_60_;
}
}
}
else
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__3));
v___x_74_ = lean_string_dec_eq(v_str_65_, v___x_73_);
if (v___x_74_ == 0)
{
return v___x_74_;
}
else
{
return v_suppressElabErrors_60_;
}
}
}
case 1:
{
lean_object* v_pre_75_; 
v_pre_75_ = lean_ctor_get(v_pre_64_, 0);
if (lean_obj_tag(v_pre_75_) == 0)
{
lean_object* v_str_76_; lean_object* v_str_77_; lean_object* v_str_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_str_76_ = lean_ctor_get(v_x_62_, 1);
v_str_77_ = lean_ctor_get(v_pre_63_, 1);
v_str_78_ = lean_ctor_get(v_pre_64_, 1);
v___x_79_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__4));
v___x_80_ = lean_string_dec_eq(v_str_78_, v___x_79_);
if (v___x_80_ == 0)
{
return v___x_80_;
}
else
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__5));
v___x_82_ = lean_string_dec_eq(v_str_77_, v___x_81_);
if (v___x_82_ == 0)
{
return v___x_82_;
}
else
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__6));
v___x_84_ = lean_string_dec_eq(v_str_76_, v___x_83_);
if (v___x_84_ == 0)
{
return v___x_84_;
}
else
{
return v_suppressElabErrors_60_;
}
}
}
}
else
{
return v___y_61_;
}
}
default: 
{
return v___y_61_;
}
}
}
case 0:
{
lean_object* v_str_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_str_85_ = lean_ctor_get(v_x_62_, 1);
v___x_86_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___closed__7));
v___x_87_ = lean_string_dec_eq(v_str_85_, v___x_86_);
if (v___x_87_ == 0)
{
return v___x_87_;
}
else
{
return v_suppressElabErrors_60_;
}
}
default: 
{
return v___y_61_;
}
}
}
else
{
return v___y_61_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_88_, lean_object* v___y_89_, lean_object* v_x_90_){
_start:
{
uint8_t v_suppressElabErrors_boxed_91_; uint8_t v___y_2765__boxed_92_; uint8_t v_res_93_; lean_object* v_r_94_; 
v_suppressElabErrors_boxed_91_ = lean_unbox(v_suppressElabErrors_88_);
v___y_2765__boxed_92_ = lean_unbox(v___y_89_);
v_res_93_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_91_, v___y_2765__boxed_92_, v_x_90_);
lean_dec(v_x_90_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_ref_96_, lean_object* v_msgData_97_, uint8_t v_severity_98_, uint8_t v_isSilent_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___y_104_; lean_object* v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; uint8_t v___y_108_; uint8_t v___y_109_; lean_object* v___y_110_; lean_object* v___y_111_; lean_object* v___y_112_; lean_object* v___y_141_; lean_object* v___y_142_; lean_object* v___y_143_; lean_object* v___y_144_; uint8_t v___y_145_; uint8_t v___y_146_; uint8_t v___y_147_; lean_object* v___y_148_; lean_object* v___y_166_; lean_object* v___y_167_; lean_object* v___y_168_; uint8_t v___y_169_; uint8_t v___y_170_; uint8_t v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_180_; uint8_t v___y_181_; uint8_t v___y_182_; uint8_t v___y_183_; uint8_t v___x_188_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; uint8_t v___y_194_; uint8_t v___y_195_; uint8_t v___y_196_; uint8_t v___y_198_; uint8_t v___x_214_; 
v___x_188_ = 2;
v___x_214_ = l_Lean_instBEqMessageSeverity_beq(v_severity_98_, v___x_188_);
if (v___x_214_ == 0)
{
v___y_198_ = v___x_214_;
goto v___jp_197_;
}
else
{
uint8_t v___x_215_; 
lean_inc_ref(v_msgData_97_);
v___x_215_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_97_);
v___y_198_ = v___x_215_;
goto v___jp_197_;
}
v___jp_103_:
{
lean_object* v___x_113_; lean_object* v_toCold_114_; lean_object* v_currNamespace_115_; lean_object* v_openDecls_116_; lean_object* v_env_117_; lean_object* v_nextMacroScope_118_; lean_object* v_ngen_119_; lean_object* v_auxDeclNGen_120_; lean_object* v_traceState_121_; lean_object* v_cache_122_; lean_object* v_messages_123_; lean_object* v_infoState_124_; lean_object* v_snapshotTasks_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_139_; 
v___x_113_ = lean_st_ref_take(v___y_112_);
v_toCold_114_ = lean_ctor_get(v___y_111_, 0);
v_currNamespace_115_ = lean_ctor_get(v_toCold_114_, 4);
v_openDecls_116_ = lean_ctor_get(v_toCold_114_, 5);
v_env_117_ = lean_ctor_get(v___x_113_, 0);
v_nextMacroScope_118_ = lean_ctor_get(v___x_113_, 1);
v_ngen_119_ = lean_ctor_get(v___x_113_, 2);
v_auxDeclNGen_120_ = lean_ctor_get(v___x_113_, 3);
v_traceState_121_ = lean_ctor_get(v___x_113_, 4);
v_cache_122_ = lean_ctor_get(v___x_113_, 5);
v_messages_123_ = lean_ctor_get(v___x_113_, 6);
v_infoState_124_ = lean_ctor_get(v___x_113_, 7);
v_snapshotTasks_125_ = lean_ctor_get(v___x_113_, 8);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_139_ == 0)
{
v___x_127_ = v___x_113_;
v_isShared_128_ = v_isSharedCheck_139_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_snapshotTasks_125_);
lean_inc(v_infoState_124_);
lean_inc(v_messages_123_);
lean_inc(v_cache_122_);
lean_inc(v_traceState_121_);
lean_inc(v_auxDeclNGen_120_);
lean_inc(v_ngen_119_);
lean_inc(v_nextMacroScope_118_);
lean_inc(v_env_117_);
lean_dec(v___x_113_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_139_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
lean_inc(v_openDecls_116_);
lean_inc(v_currNamespace_115_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_currNamespace_115_);
lean_ctor_set(v___x_129_, 1, v_openDecls_116_);
v___x_130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___y_104_);
lean_inc_ref(v___y_105_);
lean_inc_ref(v___y_106_);
v___x_131_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_131_, 0, v___y_106_);
lean_ctor_set(v___x_131_, 1, v___y_107_);
lean_ctor_set(v___x_131_, 2, v___y_110_);
lean_ctor_set(v___x_131_, 3, v___y_105_);
lean_ctor_set(v___x_131_, 4, v___x_130_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*5, v___y_109_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*5 + 1, v___y_108_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*5 + 2, v_isSilent_99_);
v___x_132_ = l_Lean_MessageLog_add(v___x_131_, v_messages_123_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 6, v___x_132_);
v___x_134_ = v___x_127_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_env_117_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_nextMacroScope_118_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_ngen_119_);
lean_ctor_set(v_reuseFailAlloc_138_, 3, v_auxDeclNGen_120_);
lean_ctor_set(v_reuseFailAlloc_138_, 4, v_traceState_121_);
lean_ctor_set(v_reuseFailAlloc_138_, 5, v_cache_122_);
lean_ctor_set(v_reuseFailAlloc_138_, 6, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_138_, 7, v_infoState_124_);
lean_ctor_set(v_reuseFailAlloc_138_, 8, v_snapshotTasks_125_);
v___x_134_ = v_reuseFailAlloc_138_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_st_ref_put(v___y_112_, v___x_134_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
}
}
v___jp_140_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_164_; 
v___x_149_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_97_);
v___x_150_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__1(v___x_149_, v___y_100_, v___y_101_);
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_164_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_164_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_164_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
lean_inc_ref_n(v___y_144_, 2);
v___x_155_ = l_Lean_FileMap_toPosition(v___y_144_, v___y_142_);
lean_dec(v___y_142_);
v___x_156_ = l_Lean_FileMap_toPosition(v___y_144_, v___y_148_);
lean_dec(v___y_148_);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
v___x_158_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___closed__0));
if (v___y_147_ == 0)
{
lean_del_object(v___x_153_);
lean_dec_ref(v___y_141_);
v___y_104_ = v_a_151_;
v___y_105_ = v___x_158_;
v___y_106_ = v___y_143_;
v___y_107_ = v___x_155_;
v___y_108_ = v___y_146_;
v___y_109_ = v___y_145_;
v___y_110_ = v___x_157_;
v___y_111_ = v___y_100_;
v___y_112_ = v___y_101_;
goto v___jp_103_;
}
else
{
uint8_t v___x_159_; 
lean_inc(v_a_151_);
v___x_159_ = l_Lean_MessageData_hasTag(v___y_141_, v_a_151_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_162_; 
lean_dec_ref_known(v___x_157_, 1);
lean_dec_ref(v___x_155_);
lean_dec(v_a_151_);
v___x_160_ = lean_box(0);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_160_);
v___x_162_ = v___x_153_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
else
{
lean_del_object(v___x_153_);
v___y_104_ = v_a_151_;
v___y_105_ = v___x_158_;
v___y_106_ = v___y_143_;
v___y_107_ = v___x_155_;
v___y_108_ = v___y_146_;
v___y_109_ = v___y_145_;
v___y_110_ = v___x_157_;
v___y_111_ = v___y_100_;
v___y_112_ = v___y_101_;
goto v___jp_103_;
}
}
}
}
v___jp_165_:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Syntax_getTailPos_x3f(v___y_172_, v___y_170_);
lean_dec(v___y_172_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_inc(v___y_173_);
v___y_141_ = v___y_166_;
v___y_142_ = v___y_173_;
v___y_143_ = v___y_167_;
v___y_144_ = v___y_168_;
v___y_145_ = v___y_170_;
v___y_146_ = v___y_169_;
v___y_147_ = v___y_171_;
v___y_148_ = v___y_173_;
goto v___jp_140_;
}
else
{
lean_object* v_val_175_; 
v_val_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_val_175_);
lean_dec_ref_known(v___x_174_, 1);
v___y_141_ = v___y_166_;
v___y_142_ = v___y_173_;
v___y_143_ = v___y_167_;
v___y_144_ = v___y_168_;
v___y_145_ = v___y_170_;
v___y_146_ = v___y_169_;
v___y_147_ = v___y_171_;
v___y_148_ = v_val_175_;
goto v___jp_140_;
}
}
v___jp_176_:
{
lean_object* v_ref_184_; lean_object* v___x_185_; 
v_ref_184_ = l_Lean_replaceRef(v_ref_96_, v___y_178_);
v___x_185_ = l_Lean_Syntax_getPos_x3f(v_ref_184_, v___y_181_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v___y_166_ = v___y_177_;
v___y_167_ = v___y_179_;
v___y_168_ = v___y_180_;
v___y_169_ = v___y_183_;
v___y_170_ = v___y_181_;
v___y_171_ = v___y_182_;
v___y_172_ = v_ref_184_;
v___y_173_ = v___x_186_;
goto v___jp_165_;
}
else
{
lean_object* v_val_187_; 
v_val_187_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_val_187_);
lean_dec_ref_known(v___x_185_, 1);
v___y_166_ = v___y_177_;
v___y_167_ = v___y_179_;
v___y_168_ = v___y_180_;
v___y_169_ = v___y_183_;
v___y_170_ = v___y_181_;
v___y_171_ = v___y_182_;
v___y_172_ = v_ref_184_;
v___y_173_ = v_val_187_;
goto v___jp_165_;
}
}
v___jp_189_:
{
if (v___y_196_ == 0)
{
v___y_177_ = v___y_190_;
v___y_178_ = v___y_193_;
v___y_179_ = v___y_191_;
v___y_180_ = v___y_192_;
v___y_181_ = v___y_194_;
v___y_182_ = v___y_195_;
v___y_183_ = v_severity_98_;
goto v___jp_176_;
}
else
{
v___y_177_ = v___y_190_;
v___y_178_ = v___y_193_;
v___y_179_ = v___y_191_;
v___y_180_ = v___y_192_;
v___y_181_ = v___y_194_;
v___y_182_ = v___y_195_;
v___y_183_ = v___x_188_;
goto v___jp_176_;
}
}
v___jp_197_:
{
if (v___y_198_ == 0)
{
lean_object* v_toCold_199_; lean_object* v_ref_200_; uint8_t v_suppressElabErrors_201_; lean_object* v_fileName_202_; lean_object* v_fileMap_203_; lean_object* v_options_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___f_207_; uint8_t v___x_208_; uint8_t v___x_209_; 
v_toCold_199_ = lean_ctor_get(v___y_100_, 0);
v_ref_200_ = lean_ctor_get(v___y_100_, 2);
v_suppressElabErrors_201_ = lean_ctor_get_uint8(v___y_100_, sizeof(void*)*3 + 1);
v_fileName_202_ = lean_ctor_get(v_toCold_199_, 0);
v_fileMap_203_ = lean_ctor_get(v_toCold_199_, 1);
v_options_204_ = lean_ctor_get(v_toCold_199_, 2);
v___x_205_ = lean_box(v_suppressElabErrors_201_);
v___x_206_ = lean_box(v___y_198_);
v___f_207_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_207_, 0, v___x_205_);
lean_closure_set(v___f_207_, 1, v___x_206_);
v___x_208_ = 1;
v___x_209_ = l_Lean_instBEqMessageSeverity_beq(v_severity_98_, v___x_208_);
if (v___x_209_ == 0)
{
v___y_190_ = v___f_207_;
v___y_191_ = v_fileName_202_;
v___y_192_ = v_fileMap_203_;
v___y_193_ = v_ref_200_;
v___y_194_ = v___y_198_;
v___y_195_ = v_suppressElabErrors_201_;
v___y_196_ = v___x_209_;
goto v___jp_189_;
}
else
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = l_Lean_warningAsError;
v___x_211_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_options_204_, v___x_210_);
v___y_190_ = v___f_207_;
v___y_191_ = v_fileName_202_;
v___y_192_ = v_fileMap_203_;
v___y_193_ = v_ref_200_;
v___y_194_ = v___y_198_;
v___y_195_ = v_suppressElabErrors_201_;
v___y_196_ = v___x_211_;
goto v___jp_189_;
}
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref(v_msgData_97_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_ref_216_, lean_object* v_msgData_217_, lean_object* v_severity_218_, lean_object* v_isSilent_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v_severity_boxed_223_; uint8_t v_isSilent_boxed_224_; lean_object* v_res_225_; 
v_severity_boxed_223_ = lean_unbox(v_severity_218_);
v_isSilent_boxed_224_ = lean_unbox(v_isSilent_219_);
v_res_225_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(v_ref_216_, v_msgData_217_, v_severity_boxed_223_, v_isSilent_boxed_224_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v_ref_216_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(lean_object* v_ref_226_, lean_object* v_msgData_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
uint8_t v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; 
v___x_231_ = 1;
v___x_232_ = 0;
v___x_233_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0_spec__0(v_ref_226_, v_msgData_227_, v___x_231_, v___x_232_, v___y_228_, v___y_229_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0___boxed(lean_object* v_ref_234_, lean_object* v_msgData_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(v_ref_234_, v_msgData_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v_ref_234_);
return v_res_239_;
}
}
static lean_object* _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
v___x_244_ = l_Lean_MessageData_ofFormat(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(lean_object* v_add_245_, lean_object* v_decl_246_, lean_object* v_stx_247_, uint8_t v_attrKind_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_obj_once(&l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_, &l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__once, _init_l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0___closed__2_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_);
v___x_253_ = l_Lean_logWarningAt___at___00__private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2__spec__0(v_stx_247_, v___x_252_, v___y_249_, v___y_250_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec_ref_known(v___x_253_, 1);
v___x_254_ = lean_box(v_attrKind_248_);
lean_inc(v___y_250_);
lean_inc_ref(v___y_249_);
v___x_255_ = lean_apply_6(v_add_245_, v_decl_246_, v_stx_247_, v___x_254_, v___y_249_, v___y_250_, lean_box(0));
return v___x_255_;
}
else
{
lean_dec(v_stx_247_);
lean_dec(v_decl_246_);
lean_dec_ref(v_add_245_);
return v___x_253_;
}
}
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
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(lean_object* v_erase_265_, lean_object* v_decl_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v___x_270_; 
lean_inc(v___y_268_);
lean_inc_ref(v___y_267_);
v___x_270_ = lean_apply_4(v_erase_265_, v_decl_266_, v___y_267_, v___y_268_, lean_box(0));
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_erase_271_, lean_object* v_decl_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(v_erase_271_, v_decl_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_334_; lean_object* v_attr_335_; lean_object* v_toAttributeImplCore_336_; lean_object* v_add_337_; lean_object* v_erase_338_; lean_object* v_descr_339_; uint8_t v_applicationTime_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___f_343_; lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_334_ = l_Lake_testDriverAttr;
v_attr_335_ = lean_ctor_get(v___x_334_, 0);
v_toAttributeImplCore_336_ = lean_ctor_get(v_attr_335_, 0);
v_add_337_ = lean_ctor_get(v_attr_335_, 1);
v_erase_338_ = lean_ctor_get(v_attr_335_, 2);
v_descr_339_ = lean_ctor_get(v_toAttributeImplCore_336_, 2);
v_applicationTime_340_ = lean_ctor_get_uint8(v_toAttributeImplCore_336_, sizeof(void*)*3);
v___x_341_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__22_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
v___x_342_ = ((lean_object*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___closed__24_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_));
lean_inc_ref(v_add_337_);
v___f_343_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__0_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed), 7, 1);
lean_closure_set(v___f_343_, 0, v_add_337_);
lean_inc_ref(v_erase_338_);
v___f_344_ = lean_alloc_closure((void*)(l___private_Lake_DSL_Attributes_0__Lake_initFn___lam__1_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_344_, 0, v_erase_338_);
lean_inc_ref(v_descr_339_);
v___x_345_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_345_, 0, v___x_341_);
lean_ctor_set(v___x_345_, 1, v___x_342_);
lean_ctor_set(v___x_345_, 2, v_descr_339_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*3, v_applicationTime_340_);
v___x_346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___f_343_);
lean_ctor_set(v___x_346_, 2, v___f_344_);
v___x_347_ = l_Lean_registerBuiltinAttribute(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2____boxed(lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lake_DSL_Attributes_0__Lake_initFn_00___x40_Lake_DSL_Attributes_945171751____hygCtx___hyg_2_();
return v_res_349_;
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
