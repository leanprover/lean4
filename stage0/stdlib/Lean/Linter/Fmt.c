// Lean compiler output
// Module: Lean.Linter.Fmt
// Imports: public import Lean.Linter.Util public import Lean.Elab.Command import Lean.Fmt.FmtM
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
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
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
lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_findChoiceResolution_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_collectSyntaxLineInfos(lean_object*);
lean_object* l_Lean_Fmt_fmt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FmtM_run___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Error_ref_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasMissing(lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fmt"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "missing"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 8, 229, 42, 239, 166, 104, 120)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(110, 124, 192, 112, 1, 27, 7, 59)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "enable the 'missing formatter' linter"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(234, 236, 195, 191, 86, 102, 217, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 199, 11, 55, 37, 150, 232, 166)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_fmt_missing;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ignorePrivate"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 8, 229, 42, 239, 166, 104, 120)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(110, 124, 192, 112, 1, 27, 7, 59)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(89, 138, 138, 89, 253, 59, 91, 6)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 149, .m_capacity = 149, .m_length = 148, .m_data = "make the 'missing formatter' linter ignore syntax with a private node kind, which is what `local syntax`, `local macro` and `local notation` produce"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(234, 236, 195, 191, 86, 102, 217, 254)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 199, 11, 55, 37, 150, 232, 166)}};
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(18, 32, 83, 52, 79, 203, 129, 2)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_fmt_missing_ignorePrivate;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__0 = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__1 = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "no auto-formatter registered for syntax kind "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__0_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Auto-formatter "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "for syntax kind "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__2 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__2_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " is incomplete.\n"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__4 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__4_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "The syntax at the location has the following form:\n\n"};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__6 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__6_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7;
static const lean_string_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__8 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__8_value;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9;
static lean_once_cell_t l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "The auto-formatter failed, so this command was not checked for missing formatters:\n\n"};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0 = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1;
static const lean_string_object l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Internal error."};
static const lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__2 = (const lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_fmtMissing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_fmtMissing___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_fmtMissing___closed__0 = (const lean_object*)&l_Lean_Linter_fmtMissing___closed__0_value;
static const lean_string_object l_Lean_Linter_fmtMissing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtMissing"};
static const lean_object* l_Lean_Linter_fmtMissing___closed__1 = (const lean_object*)&l_Lean_Linter_fmtMissing___closed__1_value;
static const lean_ctor_object l_Lean_Linter_fmtMissing___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_fmtMissing___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_fmtMissing___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_fmtMissing___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_fmtMissing___closed__2_value_aux_1),((lean_object*)&l_Lean_Linter_fmtMissing___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 92, 3, 98, 243, 31, 56, 197)}};
static const lean_object* l_Lean_Linter_fmtMissing___closed__2 = (const lean_object*)&l_Lean_Linter_fmtMissing___closed__2_value;
static const lean_ctor_object l_Lean_Linter_fmtMissing___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_fmtMissing___closed__0_value),((lean_object*)&l_Lean_Linter_fmtMissing___closed__2_value)}};
static const lean_object* l_Lean_Linter_fmtMissing___closed__3 = (const lean_object*)&l_Lean_Linter_fmtMissing___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_fmtMissing = (const lean_object*)&l_Lean_Linter_fmtMissing___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_));
v___x_83_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_));
v___x_84_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_));
v___x_85_ = l_Lean_Option_register___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4__spec__0(v___x_82_, v___x_83_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4____boxed(lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_();
return v_res_87_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(lean_object* v_opts_88_, lean_object* v_opt_89_){
_start:
{
lean_object* v_name_90_; lean_object* v_defValue_91_; lean_object* v_map_92_; lean_object* v___x_93_; 
v_name_90_ = lean_ctor_get(v_opt_89_, 0);
v_defValue_91_ = lean_ctor_get(v_opt_89_, 1);
v_map_92_ = lean_ctor_get(v_opts_88_, 0);
v___x_93_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_92_, v_name_90_);
if (lean_obj_tag(v___x_93_) == 0)
{
uint8_t v___x_94_; 
v___x_94_ = lean_unbox(v_defValue_91_);
return v___x_94_;
}
else
{
lean_object* v_val_95_; 
v_val_95_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_val_95_);
lean_dec_ref_known(v___x_93_, 1);
if (lean_obj_tag(v_val_95_) == 1)
{
uint8_t v_v_96_; 
v_v_96_ = lean_ctor_get_uint8(v_val_95_, 0);
lean_dec_ref_known(v_val_95_, 0);
return v_v_96_;
}
else
{
uint8_t v___x_97_; 
lean_dec(v_val_95_);
v___x_97_ = lean_unbox(v_defValue_91_);
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0___boxed(lean_object* v_opts_98_, lean_object* v_opt_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_opts_98_, v_opt_99_);
lean_dec_ref(v_opt_99_);
lean_dec_ref(v_opts_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(lean_object* v_opts_105_, lean_object* v_kind_106_){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___closed__1));
v___x_108_ = lean_name_eq(v_kind_106_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = l_Lean_Linter_linter_fmt_missing_ignorePrivate;
v___x_110_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_opts_105_, v___x_109_);
if (v___x_110_ == 0)
{
return v___x_110_;
}
else
{
uint8_t v___x_111_; 
v___x_111_ = l_Lean_isPrivateName(v_kind_106_);
return v___x_111_;
}
}
else
{
return v___x_108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind___boxed(lean_object* v_opts_112_, lean_object* v_kind_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(v_opts_112_, v_kind_113_);
lean_dec(v_kind_113_);
lean_dec_ref(v_opts_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__0(lean_object* v_infoState_116_, lean_object* v_x_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_trees_120_; 
v___x_118_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_116_);
v___x_119_ = lean_task_get_own(v___x_118_);
v_trees_120_ = lean_ctor_get(v___x_119_, 2);
lean_inc_ref(v_trees_120_);
lean_dec(v___x_119_);
return v_trees_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1(lean_object* v_range_124_, lean_object* v_as_125_, size_t v_sz_126_, size_t v_i_127_, lean_object* v_b_128_){
_start:
{
uint8_t v___x_129_; 
v___x_129_ = lean_usize_dec_lt(v_i_127_, v_sz_126_);
if (v___x_129_ == 0)
{
lean_dec_ref(v_range_124_);
lean_inc_ref(v_b_128_);
return v_b_128_;
}
else
{
lean_object* v___x_130_; lean_object* v_a_131_; lean_object* v___x_132_; 
v___x_130_ = lean_box(0);
v_a_131_ = lean_array_uget_borrowed(v_as_125_, v_i_127_);
lean_inc_ref(v_range_124_);
lean_inc(v_a_131_);
v___x_132_ = l_Lean_Fmt_findChoiceResolution_x3f(v_a_131_, v_range_124_);
if (lean_obj_tag(v___x_132_) == 1)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec_ref(v_range_124_);
v___x_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_130_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; size_t v___x_136_; size_t v___x_137_; 
lean_dec(v___x_132_);
v___x_135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0));
v___x_136_ = ((size_t)1ULL);
v___x_137_ = lean_usize_add(v_i_127_, v___x_136_);
v_i_127_ = v___x_137_;
v_b_128_ = v___x_135_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___boxed(lean_object* v_range_139_, lean_object* v_as_140_, lean_object* v_sz_141_, lean_object* v_i_142_, lean_object* v_b_143_){
_start:
{
size_t v_sz_boxed_144_; size_t v_i_boxed_145_; lean_object* v_res_146_; 
v_sz_boxed_144_ = lean_unbox_usize(v_sz_141_);
lean_dec(v_sz_141_);
v_i_boxed_145_ = lean_unbox_usize(v_i_142_);
lean_dec(v_i_142_);
v_res_146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1(v_range_139_, v_as_140_, v_sz_boxed_144_, v_i_boxed_145_, v_b_143_);
lean_dec_ref(v_b_143_);
lean_dec_ref(v_as_140_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(lean_object* v_range_147_, lean_object* v_x_148_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v_cs_149_; lean_object* v___x_150_; lean_object* v___x_151_; size_t v_sz_152_; size_t v___x_153_; lean_object* v___x_154_; lean_object* v_fst_155_; 
v_cs_149_ = lean_ctor_get(v_x_148_, 0);
v___x_150_ = lean_box(0);
v___x_151_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0));
v_sz_152_ = lean_array_size(v_cs_149_);
v___x_153_ = ((size_t)0ULL);
v___x_154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(v_range_147_, v_cs_149_, v_sz_152_, v___x_153_, v___x_151_);
v_fst_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_fst_155_);
lean_dec_ref(v___x_154_);
if (lean_obj_tag(v_fst_155_) == 0)
{
return v___x_150_;
}
else
{
lean_object* v_val_156_; 
v_val_156_ = lean_ctor_get(v_fst_155_, 0);
lean_inc(v_val_156_);
lean_dec_ref_known(v_fst_155_, 1);
return v_val_156_;
}
}
else
{
lean_object* v_vs_157_; lean_object* v___x_158_; lean_object* v___x_159_; size_t v_sz_160_; size_t v___x_161_; lean_object* v___x_162_; lean_object* v_fst_163_; 
v_vs_157_ = lean_ctor_get(v_x_148_, 0);
v___x_158_ = lean_box(0);
v___x_159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0));
v_sz_160_ = lean_array_size(v_vs_157_);
v___x_161_ = ((size_t)0ULL);
v___x_162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1(v_range_147_, v_vs_157_, v_sz_160_, v___x_161_, v___x_159_);
v_fst_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_fst_163_);
lean_dec_ref(v___x_162_);
if (lean_obj_tag(v_fst_163_) == 0)
{
return v___x_158_;
}
else
{
lean_object* v_val_164_; 
v_val_164_ = lean_ctor_get(v_fst_163_, 0);
lean_inc(v_val_164_);
lean_dec_ref_known(v_fst_163_, 1);
return v_val_164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(lean_object* v_range_165_, lean_object* v_as_166_, size_t v_sz_167_, size_t v_i_168_, lean_object* v_b_169_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = lean_usize_dec_lt(v_i_168_, v_sz_167_);
if (v___x_170_ == 0)
{
lean_dec_ref(v_range_165_);
lean_inc_ref(v_b_169_);
return v_b_169_;
}
else
{
lean_object* v___x_171_; lean_object* v_a_172_; lean_object* v___x_173_; 
v___x_171_ = lean_box(0);
v_a_172_ = lean_array_uget_borrowed(v_as_166_, v_i_168_);
lean_inc_ref(v_range_165_);
v___x_173_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(v_range_165_, v_a_172_);
if (lean_obj_tag(v___x_173_) == 1)
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec_ref(v_range_165_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_171_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; size_t v___x_177_; size_t v___x_178_; 
lean_dec(v___x_173_);
v___x_176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0));
v___x_177_ = ((size_t)1ULL);
v___x_178_ = lean_usize_add(v_i_168_, v___x_177_);
v_i_168_ = v___x_178_;
v_b_169_ = v___x_176_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1___boxed(lean_object* v_range_180_, lean_object* v_as_181_, lean_object* v_sz_182_, lean_object* v_i_183_, lean_object* v_b_184_){
_start:
{
size_t v_sz_boxed_185_; size_t v_i_boxed_186_; lean_object* v_res_187_; 
v_sz_boxed_185_ = lean_unbox_usize(v_sz_182_);
lean_dec(v_sz_182_);
v_i_boxed_186_ = lean_unbox_usize(v_i_183_);
lean_dec(v_i_183_);
v_res_187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0_spec__1(v_range_180_, v_as_181_, v_sz_boxed_185_, v_i_boxed_186_, v_b_184_);
lean_dec_ref(v_b_184_);
lean_dec_ref(v_as_181_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0___boxed(lean_object* v_range_188_, lean_object* v_x_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(v_range_188_, v_x_189_);
lean_dec_ref(v_x_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(lean_object* v_range_191_, lean_object* v_t_192_){
_start:
{
lean_object* v_root_193_; lean_object* v_tail_194_; lean_object* v___x_195_; 
v_root_193_ = lean_ctor_get(v_t_192_, 0);
v_tail_194_ = lean_ctor_get(v_t_192_, 1);
lean_inc_ref(v_range_191_);
v___x_195_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__0(v_range_191_, v_root_193_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v___x_196_; size_t v_sz_197_; size_t v___x_198_; lean_object* v___x_199_; lean_object* v_fst_200_; 
v___x_196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1___closed__0));
v_sz_197_ = lean_array_size(v_tail_194_);
v___x_198_ = ((size_t)0ULL);
v___x_199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0_spec__1(v_range_191_, v_tail_194_, v_sz_197_, v___x_198_, v___x_196_);
v_fst_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_fst_200_);
lean_dec_ref(v___x_199_);
if (lean_obj_tag(v_fst_200_) == 0)
{
return v___x_195_;
}
else
{
lean_object* v_val_201_; 
v_val_201_ = lean_ctor_get(v_fst_200_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v_fst_200_, 1);
return v_val_201_;
}
}
else
{
lean_dec_ref(v_range_191_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0___boxed(lean_object* v_range_202_, lean_object* v_t_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(v_range_202_, v_t_203_);
lean_dec_ref(v_t_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1(lean_object* v___x_205_, lean_object* v_range_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_thunk_get_own(v___x_205_);
v___x_208_ = l_Lean_PersistentArray_findSomeM_x3f___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__0(v_range_206_, v___x_207_);
lean_dec(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1___boxed(lean_object* v___x_209_, lean_object* v_range_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1(v___x_209_, v_range_210_);
lean_dec_ref(v___x_209_);
return v_res_211_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0(uint8_t v_suppressElabErrors_213_, uint8_t v___y_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 1)
{
lean_object* v_pre_216_; 
v_pre_216_ = lean_ctor_get(v_x_215_, 0);
if (lean_obj_tag(v_pre_216_) == 0)
{
lean_object* v_str_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_str_217_ = lean_ctor_get(v_x_215_, 1);
v___x_218_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___closed__0));
v___x_219_ = lean_string_dec_eq(v_str_217_, v___x_218_);
if (v___x_219_ == 0)
{
return v___x_219_;
}
else
{
return v_suppressElabErrors_213_;
}
}
else
{
return v___y_214_;
}
}
else
{
return v___y_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_220_, lean_object* v___y_221_, lean_object* v_x_222_){
_start:
{
uint8_t v_suppressElabErrors_boxed_223_; uint8_t v___y_8190__boxed_224_; uint8_t v_res_225_; lean_object* v_r_226_; 
v_suppressElabErrors_boxed_223_ = lean_unbox(v_suppressElabErrors_220_);
v___y_8190__boxed_224_ = lean_unbox(v___y_221_);
v_res_225_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0(v_suppressElabErrors_boxed_223_, v___y_8190__boxed_224_, v_x_222_);
lean_dec(v_x_222_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_227_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
lean_ctor_set(v___x_232_, 2, v___x_231_);
lean_ctor_set(v___x_232_, 3, v___x_231_);
lean_ctor_set(v___x_232_, 4, v___x_230_);
lean_ctor_set(v___x_232_, 5, v___x_230_);
lean_ctor_set(v___x_232_, 6, v___x_230_);
lean_ctor_set(v___x_232_, 7, v___x_230_);
lean_ctor_set(v___x_232_, 8, v___x_230_);
lean_ctor_set(v___x_232_, 9, v___x_230_);
lean_ctor_set(v___x_232_, 10, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_unsigned_to_nat(32u);
v___x_234_ = lean_mk_empty_array_with_capacity(v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_236_ = ((size_t)5ULL);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_unsigned_to_nat(32u);
v___x_239_ = lean_mk_empty_array_with_capacity(v___x_238_);
v___x_240_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3);
v___x_241_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_237_);
lean_ctor_set(v___x_241_, 3, v___x_237_);
lean_ctor_set_usize(v___x_241_, 4, v___x_236_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_242_ = lean_box(1);
v___x_243_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4);
v___x_244_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1);
v___x_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_242_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_msgData_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; lean_object* v_env_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_scopes_253_; lean_object* v___x_254_; lean_object* v_opts_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_249_ = lean_st_ref_get(v___y_247_);
v_env_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_env_250_);
lean_dec(v___x_249_);
v___x_251_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_252_ = lean_st_ref_get(v___y_247_);
v_scopes_253_ = lean_ctor_get(v___x_252_, 2);
lean_inc(v_scopes_253_);
lean_dec(v___x_252_);
v___x_254_ = l_List_head_x21___redArg(v___x_251_, v_scopes_253_);
lean_dec(v_scopes_253_);
v_opts_255_ = lean_ctor_get(v___x_254_, 1);
lean_inc_ref(v_opts_255_);
lean_dec(v___x_254_);
v___x_256_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2);
v___x_257_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5);
v___x_258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_258_, 0, v_env_250_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
lean_ctor_set(v___x_258_, 2, v___x_257_);
lean_ctor_set(v___x_258_, 3, v_opts_255_);
v___x_259_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_msgData_246_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_msgData_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v_msgData_261_, v___y_262_);
lean_dec(v___y_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(lean_object* v_ref_266_, lean_object* v_msgData_267_, uint8_t v_severity_268_, uint8_t v_isSilent_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___y_274_; lean_object* v___y_275_; uint8_t v___y_276_; uint8_t v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; uint8_t v___y_339_; uint8_t v___y_340_; uint8_t v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; uint8_t v___y_367_; uint8_t v___y_368_; uint8_t v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; uint8_t v___y_375_; uint8_t v___y_376_; uint8_t v___y_377_; uint8_t v___x_392_; uint8_t v___y_394_; uint8_t v___y_395_; uint8_t v___y_396_; uint8_t v___y_398_; uint8_t v___x_410_; 
v___x_392_ = 2;
v___x_410_ = l_Lean_instBEqMessageSeverity_beq(v_severity_268_, v___x_392_);
if (v___x_410_ == 0)
{
v___y_398_ = v___x_410_;
goto v___jp_397_;
}
else
{
uint8_t v___x_411_; 
lean_inc_ref(v_msgData_267_);
v___x_411_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_267_);
v___y_398_ = v___x_411_;
goto v___jp_397_;
}
v___jp_273_:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Elab_Command_getScope___redArg(v___y_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v_currNamespace_284_; lean_object* v___x_285_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v___x_282_, 1);
v_currNamespace_284_ = lean_ctor_get(v_a_283_, 2);
lean_inc(v_currNamespace_284_);
lean_dec(v_a_283_);
v___x_285_ = l_Lean_Elab_Command_getScope___redArg(v___y_281_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_321_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_321_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_321_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_321_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_openDecls_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_env_295_; lean_object* v_messages_296_; lean_object* v_scopes_297_; lean_object* v_usedQuotCtxts_298_; lean_object* v_nextMacroScope_299_; lean_object* v_maxRecDepth_300_; lean_object* v_ngen_301_; lean_object* v_auxDeclNGen_302_; lean_object* v_infoState_303_; lean_object* v_traceState_304_; lean_object* v_snapshotTasks_305_; lean_object* v_prevLinterStates_306_; lean_object* v_codeQualityEntryTasks_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_320_; 
v_openDecls_290_ = lean_ctor_get(v_a_286_, 3);
lean_inc(v_openDecls_290_);
lean_dec(v_a_286_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v_currNamespace_284_);
lean_ctor_set(v___x_291_, 1, v_openDecls_290_);
v___x_292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___y_278_);
lean_inc_ref(v___y_275_);
lean_inc_ref(v___y_280_);
v___x_293_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_293_, 0, v___y_280_);
lean_ctor_set(v___x_293_, 1, v___y_279_);
lean_ctor_set(v___x_293_, 2, v___y_274_);
lean_ctor_set(v___x_293_, 3, v___y_275_);
lean_ctor_set(v___x_293_, 4, v___x_292_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*5, v___y_276_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*5 + 1, v___y_277_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*5 + 2, v_isSilent_269_);
v___x_294_ = lean_st_ref_take(v___y_281_);
v_env_295_ = lean_ctor_get(v___x_294_, 0);
v_messages_296_ = lean_ctor_get(v___x_294_, 1);
v_scopes_297_ = lean_ctor_get(v___x_294_, 2);
v_usedQuotCtxts_298_ = lean_ctor_get(v___x_294_, 3);
v_nextMacroScope_299_ = lean_ctor_get(v___x_294_, 4);
v_maxRecDepth_300_ = lean_ctor_get(v___x_294_, 5);
v_ngen_301_ = lean_ctor_get(v___x_294_, 6);
v_auxDeclNGen_302_ = lean_ctor_get(v___x_294_, 7);
v_infoState_303_ = lean_ctor_get(v___x_294_, 8);
v_traceState_304_ = lean_ctor_get(v___x_294_, 9);
v_snapshotTasks_305_ = lean_ctor_get(v___x_294_, 10);
v_prevLinterStates_306_ = lean_ctor_get(v___x_294_, 11);
v_codeQualityEntryTasks_307_ = lean_ctor_get(v___x_294_, 12);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_320_ == 0)
{
v___x_309_ = v___x_294_;
v_isShared_310_ = v_isSharedCheck_320_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_codeQualityEntryTasks_307_);
lean_inc(v_prevLinterStates_306_);
lean_inc(v_snapshotTasks_305_);
lean_inc(v_traceState_304_);
lean_inc(v_infoState_303_);
lean_inc(v_auxDeclNGen_302_);
lean_inc(v_ngen_301_);
lean_inc(v_maxRecDepth_300_);
lean_inc(v_nextMacroScope_299_);
lean_inc(v_usedQuotCtxts_298_);
lean_inc(v_scopes_297_);
lean_inc(v_messages_296_);
lean_inc(v_env_295_);
lean_dec(v___x_294_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_320_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_311_ = lean_box(0);
v___x_312_ = l_Lean_MessageLog_add(v___x_293_, v_messages_296_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v___x_312_);
v___x_314_ = v___x_309_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_env_295_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_scopes_297_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_usedQuotCtxts_298_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_nextMacroScope_299_);
lean_ctor_set(v_reuseFailAlloc_319_, 5, v_maxRecDepth_300_);
lean_ctor_set(v_reuseFailAlloc_319_, 6, v_ngen_301_);
lean_ctor_set(v_reuseFailAlloc_319_, 7, v_auxDeclNGen_302_);
lean_ctor_set(v_reuseFailAlloc_319_, 8, v_infoState_303_);
lean_ctor_set(v_reuseFailAlloc_319_, 9, v_traceState_304_);
lean_ctor_set(v_reuseFailAlloc_319_, 10, v_snapshotTasks_305_);
lean_ctor_set(v_reuseFailAlloc_319_, 11, v_prevLinterStates_306_);
lean_ctor_set(v_reuseFailAlloc_319_, 12, v_codeQualityEntryTasks_307_);
v___x_314_ = v_reuseFailAlloc_319_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = lean_st_ref_put(v___y_281_, v___x_314_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_311_);
v___x_317_ = v___x_288_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_311_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec(v_currNamespace_284_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_274_);
v_a_322_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_285_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_285_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec_ref(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_274_);
v_a_330_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_282_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_282_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
v___jp_338_:
{
lean_object* v_fileName_344_; lean_object* v_fileMap_345_; uint8_t v_suppressElabErrors_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_365_; 
v_fileName_344_ = lean_ctor_get(v___y_270_, 0);
v_fileMap_345_ = lean_ctor_get(v___y_270_, 1);
v_suppressElabErrors_346_ = lean_ctor_get_uint8(v___y_270_, sizeof(void*)*10);
v___x_347_ = lean_box(v_suppressElabErrors_346_);
v___x_348_ = lean_box(v___y_339_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_349_, 0, v___x_347_);
lean_closure_set(v___f_349_, 1, v___x_348_);
v___x_350_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_267_);
v___x_351_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v___x_350_, v___y_271_);
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_365_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_365_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_365_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
lean_inc_ref_n(v_fileMap_345_, 2);
v___x_356_ = l_Lean_FileMap_toPosition(v_fileMap_345_, v___y_342_);
lean_dec(v___y_342_);
v___x_357_ = l_Lean_FileMap_toPosition(v_fileMap_345_, v___y_343_);
lean_dec(v___y_343_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
v___x_359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0));
if (v_suppressElabErrors_346_ == 0)
{
lean_del_object(v___x_354_);
lean_dec_ref(v___f_349_);
v___y_274_ = v___x_358_;
v___y_275_ = v___x_359_;
v___y_276_ = v___y_340_;
v___y_277_ = v___y_341_;
v___y_278_ = v_a_352_;
v___y_279_ = v___x_356_;
v___y_280_ = v_fileName_344_;
v___y_281_ = v___y_271_;
goto v___jp_273_;
}
else
{
uint8_t v___x_360_; 
lean_inc(v_a_352_);
v___x_360_ = l_Lean_MessageData_hasTag(v___f_349_, v_a_352_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_363_; 
lean_dec_ref_known(v___x_358_, 1);
lean_dec_ref(v___x_356_);
lean_dec(v_a_352_);
v___x_361_ = lean_box(0);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_361_);
v___x_363_ = v___x_354_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
else
{
lean_del_object(v___x_354_);
v___y_274_ = v___x_358_;
v___y_275_ = v___x_359_;
v___y_276_ = v___y_340_;
v___y_277_ = v___y_341_;
v___y_278_ = v_a_352_;
v___y_279_ = v___x_356_;
v___y_280_ = v_fileName_344_;
v___y_281_ = v___y_271_;
goto v___jp_273_;
}
}
}
}
v___jp_366_:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Syntax_getTailPos_x3f(v___y_370_, v___y_368_);
lean_dec(v___y_370_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_inc(v___y_371_);
v___y_339_ = v___y_367_;
v___y_340_ = v___y_368_;
v___y_341_ = v___y_369_;
v___y_342_ = v___y_371_;
v___y_343_ = v___y_371_;
goto v___jp_338_;
}
else
{
lean_object* v_val_373_; 
v_val_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_val_373_);
lean_dec_ref_known(v___x_372_, 1);
v___y_339_ = v___y_367_;
v___y_340_ = v___y_368_;
v___y_341_ = v___y_369_;
v___y_342_ = v___y_371_;
v___y_343_ = v_val_373_;
goto v___jp_338_;
}
}
v___jp_374_:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Elab_Command_getRef___redArg(v___y_270_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v_ref_380_; lean_object* v___x_381_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_378_, 1);
v_ref_380_ = l_Lean_replaceRef(v_ref_266_, v_a_379_);
lean_dec(v_a_379_);
v___x_381_ = l_Lean_Syntax_getPos_x3f(v_ref_380_, v___y_376_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v___y_367_ = v___y_375_;
v___y_368_ = v___y_376_;
v___y_369_ = v___y_377_;
v___y_370_ = v_ref_380_;
v___y_371_ = v___x_382_;
goto v___jp_366_;
}
else
{
lean_object* v_val_383_; 
v_val_383_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v___x_381_, 1);
v___y_367_ = v___y_375_;
v___y_368_ = v___y_376_;
v___y_369_ = v___y_377_;
v___y_370_ = v_ref_380_;
v___y_371_ = v_val_383_;
goto v___jp_366_;
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec_ref(v_msgData_267_);
v_a_384_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_378_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_378_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
v___jp_393_:
{
if (v___y_396_ == 0)
{
v___y_375_ = v___y_394_;
v___y_376_ = v___y_395_;
v___y_377_ = v_severity_268_;
goto v___jp_374_;
}
else
{
v___y_375_ = v___y_394_;
v___y_376_ = v___y_395_;
v___y_377_ = v___x_392_;
goto v___jp_374_;
}
}
v___jp_397_:
{
if (v___y_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_scopes_401_; lean_object* v___x_402_; lean_object* v_opts_403_; uint8_t v___x_404_; uint8_t v___x_405_; 
v___x_399_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_400_ = lean_st_ref_get(v___y_271_);
v_scopes_401_ = lean_ctor_get(v___x_400_, 2);
lean_inc(v_scopes_401_);
lean_dec(v___x_400_);
v___x_402_ = l_List_head_x21___redArg(v___x_399_, v_scopes_401_);
lean_dec(v_scopes_401_);
v_opts_403_ = lean_ctor_get(v___x_402_, 1);
lean_inc_ref(v_opts_403_);
lean_dec(v___x_402_);
v___x_404_ = 1;
v___x_405_ = l_Lean_instBEqMessageSeverity_beq(v_severity_268_, v___x_404_);
if (v___x_405_ == 0)
{
lean_dec_ref(v_opts_403_);
v___y_394_ = v___y_398_;
v___y_395_ = v___y_398_;
v___y_396_ = v___x_405_;
goto v___jp_393_;
}
else
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = l_Lean_warningAsError;
v___x_407_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_opts_403_, v___x_406_);
lean_dec_ref(v_opts_403_);
v___y_394_ = v___y_398_;
v___y_395_ = v___y_398_;
v___y_396_ = v___x_407_;
goto v___jp_393_;
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec_ref(v_msgData_267_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___boxed(lean_object* v_ref_412_, lean_object* v_msgData_413_, lean_object* v_severity_414_, lean_object* v_isSilent_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
uint8_t v_severity_boxed_419_; uint8_t v_isSilent_boxed_420_; lean_object* v_res_421_; 
v_severity_boxed_419_ = lean_unbox(v_severity_414_);
v_isSilent_boxed_420_ = lean_unbox(v_isSilent_415_);
v_res_421_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(v_ref_412_, v_msgData_413_, v_severity_boxed_419_, v_isSilent_boxed_420_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v_ref_412_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(lean_object* v_ref_422_, lean_object* v_msgData_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
uint8_t v___x_427_; uint8_t v___x_428_; lean_object* v___x_429_; 
v___x_427_ = 1;
v___x_428_ = 0;
v___x_429_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(v_ref_422_, v_msgData_423_, v___x_427_, v___x_428_, v___y_424_, v___y_425_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3___boxed(lean_object* v_ref_430_, lean_object* v_msgData_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(v_ref_430_, v_msgData_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v_ref_430_);
return v_res_435_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0));
v___x_438_ = l_Lean_stringToMessageData(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2));
v___x_441_ = l_Lean_stringToMessageData(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(lean_object* v_linterOption_442_, lean_object* v_stx_443_, lean_object* v_msg_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_name_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_466_; 
v_name_448_ = lean_ctor_get(v_linterOption_442_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v_linterOption_442_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v_linterOption_442_, 1);
lean_dec(v_unused_467_);
v___x_450_ = v_linterOption_442_;
v_isShared_451_ = v_isSharedCheck_466_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_name_448_);
lean_dec(v_linterOption_442_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_466_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_452_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1);
lean_inc(v_name_448_);
v___x_453_ = l_Lean_MessageData_ofName(v_name_448_);
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 7);
lean_ctor_set(v___x_450_, 1, v___x_453_);
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_455_ = v___x_450_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_453_);
v___x_455_ = v_reuseFailAlloc_465_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v_disable_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_456_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v_disable_458_ = l_Lean_MessageData_note(v___x_457_);
v___x_459_ = l_Lean_Linter_linterMessageTag;
v___x_460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_460_, 0, v_msg_444_);
lean_ctor_set(v___x_460_, 1, v_disable_458_);
v___x_461_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_459_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_462_, 0, v_name_448_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
lean_inc(v_stx_443_);
v___x_463_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_463_, 0, v_stx_443_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(v_stx_443_, v___x_463_, v___y_445_, v___y_446_);
lean_dec(v_stx_443_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___boxed(lean_object* v_linterOption_468_, lean_object* v_stx_469_, lean_object* v_msg_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v_linterOption_468_, v_stx_469_, v_msg_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_474_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__0));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(lean_object* v___x_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
if (lean_obj_tag(v_a_479_) == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v_a_480_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
else
{
lean_object* v_key_486_; lean_object* v_value_487_; lean_object* v_tail_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_key_486_ = lean_ctor_get(v_a_479_, 0);
lean_inc(v_key_486_);
v_value_487_ = lean_ctor_get(v_a_479_, 1);
lean_inc(v_value_487_);
v_tail_488_ = lean_ctor_get(v_a_479_, 2);
lean_inc(v_tail_488_);
lean_dec_ref_known(v_a_479_, 3);
v___x_489_ = lean_box(0);
v___x_490_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(v___x_478_, v_value_487_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_491_ = 1;
v___x_492_ = l_Lean_Linter_linter_fmt_missing;
v___x_493_ = l_Lean_Syntax_ofRange(v_key_486_, v___x_491_);
v___x_494_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1);
v___x_495_ = lean_box(0);
v___x_496_ = l_Lean_Expr_const___override(v_value_487_, v___x_495_);
v___x_497_ = l_Lean_MessageData_ofExpr(v___x_496_);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_494_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___x_492_, v___x_493_, v___x_498_, v___y_481_, v___y_482_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_dec_ref_known(v___x_499_, 1);
v_a_479_ = v_tail_488_;
v_a_480_ = v___x_489_;
goto _start;
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_tail_488_);
v_a_501_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_499_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_499_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_dec(v_value_487_);
lean_dec(v_key_486_);
v_a_479_ = v_tail_488_;
v_a_480_ = v___x_489_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___boxed(lean_object* v___x_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(v___x_510_, v_a_511_, v_a_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___x_510_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(lean_object* v___x_517_, lean_object* v_as_518_, size_t v_sz_519_, size_t v_i_520_, lean_object* v_b_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
uint8_t v___x_525_; 
v___x_525_ = lean_usize_dec_lt(v_i_520_, v_sz_519_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v_b_521_);
return v___x_526_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_528_; 
v_a_527_ = lean_array_uget_borrowed(v_as_518_, v_i_520_);
lean_inc(v_a_527_);
v___x_528_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(v___x_517_, v_a_527_, v_b_521_, v___y_522_, v___y_523_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_541_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_541_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_541_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_541_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
if (lean_obj_tag(v_a_529_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; 
v_a_533_ = lean_ctor_get(v_a_529_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v_a_529_, 1);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v_a_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_object* v_a_537_; size_t v___x_538_; size_t v___x_539_; 
lean_del_object(v___x_531_);
v_a_537_ = lean_ctor_get(v_a_529_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v_a_529_, 1);
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_add(v_i_520_, v___x_538_);
v_i_520_ = v___x_539_;
v_b_521_ = v_a_537_;
goto _start;
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_a_542_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_528_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_528_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4___boxed(lean_object* v___x_550_, lean_object* v_as_551_, lean_object* v_sz_552_, lean_object* v_i_553_, lean_object* v_b_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v_sz_boxed_558_ = lean_unbox_usize(v_sz_552_);
lean_dec(v_sz_552_);
v_i_boxed_559_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(v___x_550_, v_as_551_, v_sz_boxed_558_, v_i_boxed_559_, v_b_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec_ref(v_as_551_);
lean_dec_ref(v___x_550_);
return v_res_560_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0));
v___x_563_ = l_Lean_stringToMessageData(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__2));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__4));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__6));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__8));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(lean_object* v___x_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
if (lean_obj_tag(v_a_579_) == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_a_580_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
else
{
lean_object* v_value_586_; lean_object* v_key_587_; lean_object* v_tail_588_; lean_object* v_stx_589_; lean_object* v_formatterName_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_643_; 
v_value_586_ = lean_ctor_get(v_a_579_, 1);
lean_inc(v_value_586_);
v_key_587_ = lean_ctor_get(v_a_579_, 0);
lean_inc(v_key_587_);
v_tail_588_ = lean_ctor_get(v_a_579_, 2);
lean_inc(v_tail_588_);
lean_dec_ref_known(v_a_579_, 3);
v_stx_589_ = lean_ctor_get(v_value_586_, 0);
v_formatterName_590_ = lean_ctor_get(v_value_586_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_value_586_);
if (v_isSharedCheck_643_ == 0)
{
v___x_592_ = v_value_586_;
v_isShared_593_ = v_isSharedCheck_643_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_formatterName_590_);
lean_inc(v_stx_589_);
lean_dec(v_value_586_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_643_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = lean_box(0);
lean_inc(v_stx_589_);
v___x_595_ = l_Lean_Syntax_getKind(v_stx_589_);
v___x_596_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(v___x_578_, v___x_595_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; lean_object* v___y_599_; uint8_t v___x_640_; 
v___x_597_ = 1;
v___x_640_ = l_Lean_Name_isAnonymous(v_formatterName_590_);
if (v___x_640_ == 0)
{
goto v___jp_634_;
}
else
{
if (v___x_596_ == 0)
{
lean_object* v___x_641_; 
lean_dec(v_formatterName_590_);
v___x_641_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10);
v___y_599_ = v___x_641_;
goto v___jp_598_;
}
else
{
goto v___jp_634_;
}
}
v___jp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_600_ = l_Lean_Linter_linter_fmt_missing;
v___x_601_ = l_Lean_Syntax_ofRange(v_key_587_, v___x_597_);
v___x_602_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1);
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 7);
lean_ctor_set(v___x_592_, 1, v___y_599_);
lean_ctor_set(v___x_592_, 0, v___x_602_);
v___x_604_ = v___x_592_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___y_599_);
v___x_604_ = v_reuseFailAlloc_633_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_605_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_box(0);
v___x_608_ = l_Lean_Expr_const___override(v___x_595_, v___x_607_);
v___x_609_ = l_Lean_MessageData_ofExpr(v___x_608_);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_606_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_box(0);
v___x_616_ = l_Lean_Syntax_formatStx(v_stx_589_, v___x_615_, v___x_596_);
v___x_617_ = l_Std_Format_defWidth;
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = l_Std_Format_pretty(v___x_616_, v___x_617_, v___x_618_, v___x_618_);
v___x_620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
v___x_621_ = l_Lean_MessageData_ofFormat(v___x_620_);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_614_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___x_600_, v___x_601_, v___x_622_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_dec_ref_known(v___x_623_, 1);
v_a_579_ = v_tail_588_;
v_a_580_ = v___x_594_;
goto _start;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_tail_588_);
v_a_625_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_623_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
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
}
v___jp_634_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_635_ = lean_box(0);
v___x_636_ = l_Lean_Expr_const___override(v_formatterName_590_, v___x_635_);
v___x_637_ = l_Lean_MessageData_ofExpr(v___x_636_);
v___x_638_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___y_599_ = v___x_639_;
goto v___jp_598_;
}
}
else
{
lean_dec(v___x_595_);
lean_del_object(v___x_592_);
lean_dec(v_formatterName_590_);
lean_dec(v_stx_589_);
lean_dec(v_key_587_);
v_a_579_ = v_tail_588_;
v_a_580_ = v___x_594_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___boxed(lean_object* v___x_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(v___x_644_, v_a_645_, v_a_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec_ref(v___x_644_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(lean_object* v___x_651_, lean_object* v_as_652_, size_t v_sz_653_, size_t v_i_654_, lean_object* v_b_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = lean_usize_dec_lt(v_i_654_, v_sz_653_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v_b_655_);
return v___x_660_;
}
else
{
lean_object* v_a_661_; lean_object* v___x_662_; 
v_a_661_ = lean_array_uget_borrowed(v_as_652_, v_i_654_);
lean_inc(v_a_661_);
v___x_662_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(v___x_651_, v_a_661_, v_b_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_675_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_675_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
if (lean_obj_tag(v_a_663_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; 
v_a_667_ = lean_ctor_get(v_a_663_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v_a_663_, 1);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v_a_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
else
{
lean_object* v_a_671_; size_t v___x_672_; size_t v___x_673_; 
lean_del_object(v___x_665_);
v_a_671_ = lean_ctor_get(v_a_663_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v_a_663_, 1);
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_654_, v___x_672_);
v_i_654_ = v___x_673_;
v_b_655_ = v_a_671_;
goto _start;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
v_a_676_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_662_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_662_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5___boxed(lean_object* v___x_684_, lean_object* v_as_685_, lean_object* v_sz_686_, lean_object* v_i_687_, lean_object* v_b_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
size_t v_sz_boxed_692_; size_t v_i_boxed_693_; lean_object* v_res_694_; 
v_sz_boxed_692_ = lean_unbox_usize(v_sz_686_);
lean_dec(v_sz_686_);
v_i_boxed_693_ = lean_unbox_usize(v_i_687_);
lean_dec(v_i_687_);
v_res_694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(v___x_684_, v_as_685_, v_sz_boxed_692_, v_i_boxed_693_, v_b_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec_ref(v_as_685_);
lean_dec_ref(v___x_684_);
return v_res_694_;
}
}
static lean_object* _init_l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(lean_object* v_stx_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_703_; lean_object* v_env_704_; lean_object* v_fileMap_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_scopes_708_; lean_object* v___x_709_; lean_object* v_opts_710_; lean_object* v___x_711_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v_infoState_730_; lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_703_ = lean_st_ref_get(v_a_701_);
v_env_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc_ref(v_env_704_);
lean_dec(v___x_703_);
v_fileMap_705_ = lean_ctor_get(v_a_700_, 1);
v___x_706_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_707_ = lean_st_ref_get(v_a_701_);
v_scopes_708_ = lean_ctor_get(v___x_707_, 2);
lean_inc(v_scopes_708_);
lean_dec(v___x_707_);
v___x_709_ = l_List_head_x21___redArg(v___x_706_, v_scopes_708_);
lean_dec(v_scopes_708_);
v_opts_710_ = lean_ctor_get(v___x_709_, 1);
lean_inc_ref_n(v_opts_710_, 2);
lean_dec(v___x_709_);
v___x_711_ = lean_st_ref_get(v_a_701_);
v_infoState_730_ = lean_ctor_get(v___x_711_, 8);
lean_inc_ref(v_infoState_730_);
lean_dec(v___x_711_);
v___f_731_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__0), 2, 1);
lean_closure_set(v___f_731_, 0, v_infoState_730_);
v___x_732_ = lean_mk_thunk(v___f_731_);
v___f_733_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1___boxed), 2, 1);
lean_closure_set(v___f_733_, 0, v___x_732_);
lean_inc_n(v_stx_699_, 2);
v___x_734_ = l_Lean_Fmt_collectSyntaxLineInfos(v_stx_699_);
lean_inc_ref(v_fileMap_705_);
v___x_735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_735_, 0, v_env_704_);
lean_ctor_set(v___x_735_, 1, v_fileMap_705_);
lean_ctor_set(v___x_735_, 2, v___f_733_);
lean_ctor_set(v___x_735_, 3, v_opts_710_);
lean_ctor_set(v___x_735_, 4, v___x_734_);
v___x_736_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 1);
lean_closure_set(v___x_736_, 0, v_stx_699_);
v___x_737_ = l_Lean_FmtM_run___redArg(v___x_735_, v___x_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___y_740_; lean_object* v___x_752_; 
lean_dec_ref(v_opts_710_);
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc_n(v_a_738_, 2);
lean_dec_ref_known(v___x_737_, 1);
v___x_752_ = l_Lean_Fmt_Error_ref_x3f(v_a_738_);
if (lean_obj_tag(v___x_752_) == 0)
{
v___y_740_ = v_stx_699_;
goto v___jp_739_;
}
else
{
lean_object* v_val_753_; 
lean_dec(v_stx_699_);
v_val_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v___x_752_, 1);
v___y_740_ = v_val_753_;
goto v___jp_739_;
}
v___jp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = l_Lean_Linter_linter_fmt_missing;
v___x_742_ = lean_obj_once(&l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1, &l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1_once, _init_l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1);
switch(lean_obj_tag(v_a_738_))
{
case 0:
{
lean_object* v___x_743_; 
lean_dec_ref_known(v_a_738_, 0);
v___x_743_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__2));
v___y_713_ = v___y_740_;
v___y_714_ = v___x_742_;
v___y_715_ = v___x_741_;
v___y_716_ = v___x_743_;
goto v___jp_712_;
}
case 1:
{
lean_object* v_err_744_; 
v_err_744_ = lean_ctor_get(v_a_738_, 0);
lean_inc_ref(v_err_744_);
lean_dec_ref_known(v_a_738_, 1);
if (lean_obj_tag(v_err_744_) == 0)
{
lean_object* v_msg_745_; 
v_msg_745_ = lean_ctor_get(v_err_744_, 0);
lean_inc_ref(v_msg_745_);
lean_dec_ref_known(v_err_744_, 1);
v___y_713_ = v___y_740_;
v___y_714_ = v___x_742_;
v___y_715_ = v___x_741_;
v___y_716_ = v_msg_745_;
goto v___jp_712_;
}
else
{
lean_object* v_msg_746_; 
v_msg_746_ = lean_ctor_get(v_err_744_, 1);
lean_inc_ref(v_msg_746_);
lean_dec_ref(v_err_744_);
v___y_713_ = v___y_740_;
v___y_714_ = v___x_742_;
v___y_715_ = v___x_741_;
v___y_716_ = v_msg_746_;
goto v___jp_712_;
}
}
case 2:
{
lean_object* v_err_747_; 
v_err_747_ = lean_ctor_get(v_a_738_, 0);
lean_inc_ref(v_err_747_);
lean_dec_ref_known(v_a_738_, 1);
if (lean_obj_tag(v_err_747_) == 0)
{
lean_object* v_msg_748_; 
v_msg_748_ = lean_ctor_get(v_err_747_, 2);
lean_inc_ref(v_msg_748_);
lean_dec_ref_known(v_err_747_, 3);
v___y_713_ = v___y_740_;
v___y_714_ = v___x_742_;
v___y_715_ = v___x_741_;
v___y_716_ = v_msg_748_;
goto v___jp_712_;
}
else
{
lean_object* v_msg_749_; 
v_msg_749_ = lean_ctor_get(v_err_747_, 1);
lean_inc_ref(v_msg_749_);
lean_dec_ref_known(v_err_747_, 2);
v___y_713_ = v___y_740_;
v___y_714_ = v___x_742_;
v___y_715_ = v___x_741_;
v___y_716_ = v_msg_749_;
goto v___jp_712_;
}
}
default: 
{
lean_object* v_err_750_; lean_object* v_msg_751_; 
v_err_750_ = lean_ctor_get(v_a_738_, 0);
lean_inc_ref(v_err_750_);
lean_dec_ref_known(v_a_738_, 1);
v_msg_751_ = lean_ctor_get(v_err_750_, 1);
lean_inc_ref(v_msg_751_);
lean_dec_ref(v_err_750_);
v___y_713_ = v___y_740_;
v___y_714_ = v___x_742_;
v___y_715_ = v___x_741_;
v___y_716_ = v_msg_751_;
goto v___jp_712_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v_toState_755_; lean_object* v_missingFormatters_756_; lean_object* v_partialFormatters_757_; lean_object* v_buckets_758_; lean_object* v___x_759_; size_t v_sz_760_; size_t v___x_761_; lean_object* v___x_762_; 
lean_dec(v_stx_699_);
v_a_754_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_737_, 1);
v_toState_755_ = lean_ctor_get(v_a_754_, 0);
lean_inc_ref(v_toState_755_);
lean_dec(v_a_754_);
v_missingFormatters_756_ = lean_ctor_get(v_toState_755_, 3);
lean_inc_ref(v_missingFormatters_756_);
v_partialFormatters_757_ = lean_ctor_get(v_toState_755_, 4);
lean_inc_ref(v_partialFormatters_757_);
lean_dec_ref(v_toState_755_);
v_buckets_758_ = lean_ctor_get(v_missingFormatters_756_, 1);
lean_inc_ref(v_buckets_758_);
lean_dec_ref(v_missingFormatters_756_);
v___x_759_ = lean_box(0);
v_sz_760_ = lean_array_size(v_buckets_758_);
v___x_761_ = ((size_t)0ULL);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(v_opts_710_, v_buckets_758_, v_sz_760_, v___x_761_, v___x_759_, v_a_700_, v_a_701_);
lean_dec_ref(v_buckets_758_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_buckets_763_; size_t v_sz_764_; lean_object* v___x_765_; 
lean_dec_ref_known(v___x_762_, 1);
v_buckets_763_ = lean_ctor_get(v_partialFormatters_757_, 1);
lean_inc_ref(v_buckets_763_);
lean_dec_ref(v_partialFormatters_757_);
v_sz_764_ = lean_array_size(v_buckets_763_);
v___x_765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(v_opts_710_, v_buckets_763_, v_sz_764_, v___x_761_, v___x_759_, v_a_700_, v_a_701_);
lean_dec_ref(v_buckets_763_);
lean_dec_ref(v_opts_710_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v___x_765_, 0);
lean_dec(v_unused_773_);
v___x_767_ = v___x_765_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_dec(v___x_765_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_759_);
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_759_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
return v___x_765_;
}
}
else
{
lean_dec_ref(v_partialFormatters_757_);
lean_dec_ref(v_opts_710_);
return v___x_762_;
}
}
v___jp_712_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_717_, 0, v___y_716_);
v___x_718_ = l_Lean_MessageData_ofFormat(v___x_717_);
lean_inc_ref(v___y_714_);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___y_714_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
lean_inc_ref(v___y_715_);
v___x_720_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___y_715_, v___y_713_, v___x_719_, v_a_700_, v_a_701_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v___x_720_, 0);
lean_dec(v_unused_729_);
v___x_722_ = v___x_720_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_dec(v___x_720_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = lean_box(0);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_724_);
v___x_726_ = v___x_722_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
else
{
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___boxed(lean_object* v_stx_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(v_stx_774_, v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10(lean_object* v_msgData_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v_msgData_779_, v___y_781_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_msgData_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10(v_msgData_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(lean_object* v_o_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v_env_794_; lean_object* v___x_795_; lean_object* v_toEnvExtension_796_; lean_object* v_asyncMode_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v_merged_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v___x_792_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_793_ = lean_st_ref_get(v___y_790_);
v_env_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc_ref(v_env_794_);
lean_dec(v___x_793_);
v___x_795_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_796_ = lean_ctor_get(v___x_795_, 0);
v_asyncMode_797_ = lean_ctor_get(v_toEnvExtension_796_, 2);
v___x_798_ = lean_box(0);
v___x_799_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_792_, v___x_795_, v_env_794_, v_asyncMode_797_, v___x_798_);
v_merged_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___x_799_, 1);
lean_dec(v_unused_809_);
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_merged_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v_merged_800_);
lean_ctor_set(v___x_802_, 0, v_o_789_);
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_o_789_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_merged_800_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg___boxed(lean_object* v_o_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_o_810_, v___y_811_);
lean_dec(v___y_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_scopes_819_; lean_object* v___x_820_; lean_object* v_opts_821_; lean_object* v___x_822_; 
v___x_817_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_818_ = lean_st_ref_get(v___y_815_);
v_scopes_819_ = lean_ctor_get(v___x_818_, 2);
lean_inc(v_scopes_819_);
lean_dec(v___x_818_);
v___x_820_ = l_List_head_x21___redArg(v___x_817_, v_scopes_819_);
lean_dec(v_scopes_819_);
v_opts_821_ = lean_ctor_get(v___x_820_, 1);
lean_inc_ref(v_opts_821_);
lean_dec(v___x_820_);
v___x_822_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_opts_821_, v___y_815_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0___boxed(lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0(lean_object* v_cmdStx_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_849_; 
v___x_831_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(v___y_828_, v___y_829_);
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_849_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_849_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_849_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_toOptions_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v_toOptions_836_ = lean_ctor_get(v_a_832_, 0);
lean_inc_ref(v_toOptions_836_);
lean_dec(v_a_832_);
v___x_837_ = l_Lean_Linter_linter_fmt_missing;
v___x_838_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_toOptions_836_, v___x_837_);
lean_dec_ref(v_toOptions_836_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_841_; 
lean_dec(v_cmdStx_827_);
v___x_839_ = lean_box(0);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_839_);
v___x_841_ = v___x_834_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
else
{
uint8_t v___x_843_; 
v___x_843_ = l_Lean_Syntax_hasMissing(v_cmdStx_827_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_del_object(v___x_834_);
v___x_844_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(v_cmdStx_827_, v___y_828_, v___y_829_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_847_; 
lean_dec(v_cmdStx_827_);
v___x_845_ = lean_box(0);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_845_);
v___x_847_ = v___x_834_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0___boxed(lean_object* v_cmdStx_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Linter_fmtMissing___lam__0(v_cmdStx_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0(lean_object* v_o_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_o_865_, v___y_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___boxed(lean_object* v_o_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0(v_o_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_Linter_fmtMissing));
v___x_877_ = l_Lean_Elab_Command_addLinter(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2____boxed(lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_();
return v_res_879_;
}
}
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Fmt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2648254671____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_fmt_missing = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_fmt_missing);
lean_dec_ref(res);
res = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_2307285549____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_fmt_missing_ignorePrivate = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_fmt_missing_ignorePrivate);
lean_dec_ref(res);
res = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Fmt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Fmt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Fmt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Fmt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Fmt(builtin);
}
#ifdef __cplusplus
}
#endif
