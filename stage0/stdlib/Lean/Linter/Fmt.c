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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0(uint8_t v_suppressElabErrors_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 1)
{
lean_object* v_pre_215_; 
v_pre_215_ = lean_ctor_get(v_x_214_, 0);
if (lean_obj_tag(v_pre_215_) == 0)
{
lean_object* v_str_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_str_216_ = lean_ctor_get(v_x_214_, 1);
v___x_217_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___closed__0));
v___x_218_ = lean_string_dec_eq(v_str_216_, v___x_217_);
if (v___x_218_ == 0)
{
return v___x_218_;
}
else
{
return v_suppressElabErrors_213_;
}
}
else
{
uint8_t v___x_219_; 
v___x_219_ = 0;
return v___x_219_;
}
}
else
{
uint8_t v___x_220_; 
v___x_220_ = 0;
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_221_, lean_object* v_x_222_){
_start:
{
uint8_t v_suppressElabErrors_boxed_223_; uint8_t v_res_224_; lean_object* v_r_225_; 
v_suppressElabErrors_boxed_223_ = lean_unbox(v_suppressElabErrors_221_);
v_res_224_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0(v_suppressElabErrors_boxed_223_, v_x_222_);
lean_dec(v_x_222_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_226_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__0);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
lean_ctor_set(v___x_231_, 3, v___x_230_);
lean_ctor_set(v___x_231_, 4, v___x_229_);
lean_ctor_set(v___x_231_, 5, v___x_229_);
lean_ctor_set(v___x_231_, 6, v___x_229_);
lean_ctor_set(v___x_231_, 7, v___x_229_);
lean_ctor_set(v___x_231_, 8, v___x_229_);
lean_ctor_set(v___x_231_, 9, v___x_229_);
lean_ctor_set(v___x_231_, 10, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_unsigned_to_nat(32u);
v___x_233_ = lean_mk_empty_array_with_capacity(v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_235_ = ((size_t)5ULL);
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_unsigned_to_nat(32u);
v___x_238_ = lean_mk_empty_array_with_capacity(v___x_237_);
v___x_239_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__3);
v___x_240_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_238_);
lean_ctor_set(v___x_240_, 2, v___x_236_);
lean_ctor_set(v___x_240_, 3, v___x_236_);
lean_ctor_set_usize(v___x_240_, 4, v___x_235_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_241_ = lean_box(1);
v___x_242_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__4);
v___x_243_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1);
v___x_244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
lean_ctor_set(v___x_244_, 2, v___x_241_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(lean_object* v_msgData_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; lean_object* v_env_249_; uint8_t v___x_250_; lean_object* v_env_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_scopes_254_; lean_object* v___x_255_; lean_object* v_opts_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_248_ = lean_st_ref_get(v___y_246_);
v_env_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc_ref(v_env_249_);
lean_dec(v___x_248_);
v___x_250_ = 0;
v_env_251_ = l_Lean_Environment_setRecordingDeps(v_env_249_, v___x_250_);
v___x_252_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_253_ = lean_st_ref_get(v___y_246_);
v_scopes_254_ = lean_ctor_get(v___x_253_, 2);
lean_inc(v_scopes_254_);
lean_dec(v___x_253_);
v___x_255_ = l_List_head_x21___redArg(v___x_252_, v_scopes_254_);
lean_dec(v_scopes_254_);
v_opts_256_ = lean_ctor_get(v___x_255_, 1);
lean_inc_ref(v_opts_256_);
lean_dec(v___x_255_);
v___x_257_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2);
v___x_258_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5);
v___x_259_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_259_, 0, v_env_251_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
lean_ctor_set(v___x_259_, 2, v___x_258_);
lean_ctor_set(v___x_259_, 3, v_opts_256_);
v___x_260_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_msgData_245_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_msgData_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v_msgData_262_, v___y_263_);
lean_dec(v___y_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(lean_object* v_ref_267_, lean_object* v_msgData_268_, uint8_t v_severity_269_, uint8_t v_isSilent_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; uint8_t v___y_280_; uint8_t v___y_281_; lean_object* v___y_282_; lean_object* v___y_340_; uint8_t v___y_341_; uint8_t v___y_342_; lean_object* v___y_343_; lean_object* v___y_366_; uint8_t v___y_367_; uint8_t v___y_368_; lean_object* v___y_369_; uint8_t v___y_373_; uint8_t v___y_374_; uint8_t v___x_389_; uint8_t v___y_391_; uint8_t v___x_401_; 
v___x_389_ = 2;
v___x_401_ = l_Lean_instBEqMessageSeverity_beq(v_severity_269_, v___x_389_);
if (v___x_401_ == 0)
{
v___y_391_ = v___x_401_;
goto v___jp_390_;
}
else
{
uint8_t v___x_402_; 
lean_inc_ref(v_msgData_268_);
v___x_402_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_268_);
if (v___x_402_ == 0)
{
v___y_391_ = v___x_402_;
goto v___jp_390_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref(v_msgData_268_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
v___jp_274_:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Elab_Command_getScope___redArg(v___y_282_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v_currNamespace_285_; lean_object* v___x_286_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_283_, 1);
v_currNamespace_285_ = lean_ctor_get(v_a_284_, 2);
lean_inc(v_currNamespace_285_);
lean_dec(v_a_284_);
v___x_286_ = l_Lean_Elab_Command_getScope___redArg(v___y_282_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_322_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_322_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_322_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_322_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v_openDecls_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_env_296_; lean_object* v_messages_297_; lean_object* v_scopes_298_; lean_object* v_usedQuotCtxts_299_; lean_object* v_nextMacroScope_300_; lean_object* v_maxRecDepth_301_; lean_object* v_ngen_302_; lean_object* v_auxDeclNGen_303_; lean_object* v_infoState_304_; lean_object* v_traceState_305_; lean_object* v_snapshotTasks_306_; lean_object* v_prevLinterStates_307_; lean_object* v_codeQualityEntryTasks_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_321_; 
v_openDecls_291_ = lean_ctor_get(v_a_287_, 3);
lean_inc(v_openDecls_291_);
lean_dec(v_a_287_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_currNamespace_285_);
lean_ctor_set(v___x_292_, 1, v_openDecls_291_);
v___x_293_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___y_278_);
lean_inc_ref(v___y_276_);
lean_inc_ref(v___y_279_);
v___x_294_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_294_, 0, v___y_279_);
lean_ctor_set(v___x_294_, 1, v___y_275_);
lean_ctor_set(v___x_294_, 2, v___y_277_);
lean_ctor_set(v___x_294_, 3, v___y_276_);
lean_ctor_set(v___x_294_, 4, v___x_293_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*5, v___y_280_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*5 + 1, v___y_281_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*5 + 2, v_isSilent_270_);
v___x_295_ = lean_st_ref_take(v___y_282_);
v_env_296_ = lean_ctor_get(v___x_295_, 0);
v_messages_297_ = lean_ctor_get(v___x_295_, 1);
v_scopes_298_ = lean_ctor_get(v___x_295_, 2);
v_usedQuotCtxts_299_ = lean_ctor_get(v___x_295_, 3);
v_nextMacroScope_300_ = lean_ctor_get(v___x_295_, 4);
v_maxRecDepth_301_ = lean_ctor_get(v___x_295_, 5);
v_ngen_302_ = lean_ctor_get(v___x_295_, 6);
v_auxDeclNGen_303_ = lean_ctor_get(v___x_295_, 7);
v_infoState_304_ = lean_ctor_get(v___x_295_, 8);
v_traceState_305_ = lean_ctor_get(v___x_295_, 9);
v_snapshotTasks_306_ = lean_ctor_get(v___x_295_, 10);
v_prevLinterStates_307_ = lean_ctor_get(v___x_295_, 11);
v_codeQualityEntryTasks_308_ = lean_ctor_get(v___x_295_, 12);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_321_ == 0)
{
v___x_310_ = v___x_295_;
v_isShared_311_ = v_isSharedCheck_321_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_codeQualityEntryTasks_308_);
lean_inc(v_prevLinterStates_307_);
lean_inc(v_snapshotTasks_306_);
lean_inc(v_traceState_305_);
lean_inc(v_infoState_304_);
lean_inc(v_auxDeclNGen_303_);
lean_inc(v_ngen_302_);
lean_inc(v_maxRecDepth_301_);
lean_inc(v_nextMacroScope_300_);
lean_inc(v_usedQuotCtxts_299_);
lean_inc(v_scopes_298_);
lean_inc(v_messages_297_);
lean_inc(v_env_296_);
lean_dec(v___x_295_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_321_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v___x_312_ = lean_box(0);
v___x_313_ = l_Lean_MessageLog_add(v___x_294_, v_messages_297_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v___x_313_);
v___x_315_ = v___x_310_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_env_296_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_scopes_298_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_usedQuotCtxts_299_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v_nextMacroScope_300_);
lean_ctor_set(v_reuseFailAlloc_320_, 5, v_maxRecDepth_301_);
lean_ctor_set(v_reuseFailAlloc_320_, 6, v_ngen_302_);
lean_ctor_set(v_reuseFailAlloc_320_, 7, v_auxDeclNGen_303_);
lean_ctor_set(v_reuseFailAlloc_320_, 8, v_infoState_304_);
lean_ctor_set(v_reuseFailAlloc_320_, 9, v_traceState_305_);
lean_ctor_set(v_reuseFailAlloc_320_, 10, v_snapshotTasks_306_);
lean_ctor_set(v_reuseFailAlloc_320_, 11, v_prevLinterStates_307_);
lean_ctor_set(v_reuseFailAlloc_320_, 12, v_codeQualityEntryTasks_308_);
v___x_315_ = v_reuseFailAlloc_320_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lean_st_ref_put(v___y_282_, v___x_315_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_312_);
v___x_318_ = v___x_289_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_312_);
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
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec(v_currNamespace_285_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_275_);
v_a_323_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_286_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_286_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_275_);
v_a_331_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_283_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_283_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
v___jp_339_:
{
lean_object* v_fileName_344_; lean_object* v_fileMap_345_; uint8_t v_suppressElabErrors_346_; lean_object* v___x_347_; lean_object* v___f_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_364_; 
v_fileName_344_ = lean_ctor_get(v___y_271_, 0);
v_fileMap_345_ = lean_ctor_get(v___y_271_, 1);
v_suppressElabErrors_346_ = lean_ctor_get_uint8(v___y_271_, sizeof(void*)*10);
v___x_347_ = lean_box(v_suppressElabErrors_346_);
v___f_348_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_348_, 0, v___x_347_);
v___x_349_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_268_);
v___x_350_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v___x_349_, v___y_272_);
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_364_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_364_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_364_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
lean_inc_ref_n(v_fileMap_345_, 2);
v___x_355_ = l_Lean_FileMap_toPosition(v_fileMap_345_, v___y_340_);
lean_dec(v___y_340_);
v___x_356_ = l_Lean_FileMap_toPosition(v_fileMap_345_, v___y_343_);
lean_dec(v___y_343_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
v___x_358_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0));
if (v_suppressElabErrors_346_ == 0)
{
lean_del_object(v___x_353_);
lean_dec_ref(v___f_348_);
v___y_275_ = v___x_355_;
v___y_276_ = v___x_358_;
v___y_277_ = v___x_357_;
v___y_278_ = v_a_351_;
v___y_279_ = v_fileName_344_;
v___y_280_ = v___y_341_;
v___y_281_ = v___y_342_;
v___y_282_ = v___y_272_;
goto v___jp_274_;
}
else
{
uint8_t v___x_359_; 
lean_inc(v_a_351_);
v___x_359_ = l_Lean_MessageData_hasTag(v___f_348_, v_a_351_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_362_; 
lean_dec_ref_known(v___x_357_, 1);
lean_dec_ref(v___x_355_);
lean_dec(v_a_351_);
v___x_360_ = lean_box(0);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_360_);
v___x_362_ = v___x_353_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
else
{
lean_del_object(v___x_353_);
v___y_275_ = v___x_355_;
v___y_276_ = v___x_358_;
v___y_277_ = v___x_357_;
v___y_278_ = v_a_351_;
v___y_279_ = v_fileName_344_;
v___y_280_ = v___y_341_;
v___y_281_ = v___y_342_;
v___y_282_ = v___y_272_;
goto v___jp_274_;
}
}
}
}
v___jp_365_:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Syntax_getTailPos_x3f(v___y_366_, v___y_367_);
lean_dec(v___y_366_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_inc(v___y_369_);
v___y_340_ = v___y_369_;
v___y_341_ = v___y_367_;
v___y_342_ = v___y_368_;
v___y_343_ = v___y_369_;
goto v___jp_339_;
}
else
{
lean_object* v_val_371_; 
v_val_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v___x_370_, 1);
v___y_340_ = v___y_369_;
v___y_341_ = v___y_367_;
v___y_342_ = v___y_368_;
v___y_343_ = v_val_371_;
goto v___jp_339_;
}
}
v___jp_372_:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Elab_Command_getRef___redArg(v___y_271_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v_ref_377_; lean_object* v___x_378_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v___x_375_, 1);
v_ref_377_ = l_Lean_replaceRef(v_ref_267_, v_a_376_);
lean_dec(v_a_376_);
v___x_378_ = l_Lean_Syntax_getPos_x3f(v_ref_377_, v___y_373_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v___y_366_ = v_ref_377_;
v___y_367_ = v___y_373_;
v___y_368_ = v___y_374_;
v___y_369_ = v___x_379_;
goto v___jp_365_;
}
else
{
lean_object* v_val_380_; 
v_val_380_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_val_380_);
lean_dec_ref_known(v___x_378_, 1);
v___y_366_ = v_ref_377_;
v___y_367_ = v___y_373_;
v___y_368_ = v___y_374_;
v___y_369_ = v_val_380_;
goto v___jp_365_;
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v_msgData_268_);
v_a_381_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_375_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_375_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
v___jp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_scopes_394_; lean_object* v___x_395_; lean_object* v_opts_396_; uint8_t v___x_397_; uint8_t v___x_398_; 
v___x_392_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_393_ = lean_st_ref_get(v___y_272_);
v_scopes_394_ = lean_ctor_get(v___x_393_, 2);
lean_inc(v_scopes_394_);
lean_dec(v___x_393_);
v___x_395_ = l_List_head_x21___redArg(v___x_392_, v_scopes_394_);
lean_dec(v_scopes_394_);
v_opts_396_ = lean_ctor_get(v___x_395_, 1);
lean_inc_ref(v_opts_396_);
lean_dec(v___x_395_);
v___x_397_ = 1;
v___x_398_ = l_Lean_instBEqMessageSeverity_beq(v_severity_269_, v___x_397_);
if (v___x_398_ == 0)
{
lean_dec_ref(v_opts_396_);
v___y_373_ = v___y_391_;
v___y_374_ = v_severity_269_;
goto v___jp_372_;
}
else
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = l_Lean_warningAsError;
v___x_400_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_opts_396_, v___x_399_);
lean_dec_ref(v_opts_396_);
if (v___x_400_ == 0)
{
v___y_373_ = v___y_391_;
v___y_374_ = v_severity_269_;
goto v___jp_372_;
}
else
{
v___y_373_ = v___y_391_;
v___y_374_ = v___x_389_;
goto v___jp_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___boxed(lean_object* v_ref_405_, lean_object* v_msgData_406_, lean_object* v_severity_407_, lean_object* v_isSilent_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v_severity_boxed_412_; uint8_t v_isSilent_boxed_413_; lean_object* v_res_414_; 
v_severity_boxed_412_ = lean_unbox(v_severity_407_);
v_isSilent_boxed_413_ = lean_unbox(v_isSilent_408_);
v_res_414_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(v_ref_405_, v_msgData_406_, v_severity_boxed_412_, v_isSilent_boxed_413_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v_ref_405_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(lean_object* v_ref_415_, lean_object* v_msgData_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
uint8_t v___x_420_; uint8_t v___x_421_; lean_object* v___x_422_; 
v___x_420_ = 1;
v___x_421_ = 0;
v___x_422_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(v_ref_415_, v_msgData_416_, v___x_420_, v___x_421_, v___y_417_, v___y_418_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3___boxed(lean_object* v_ref_423_, lean_object* v_msgData_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(v_ref_423_, v_msgData_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v_ref_423_);
return v_res_428_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0));
v___x_431_ = l_Lean_stringToMessageData(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2));
v___x_434_ = l_Lean_stringToMessageData(v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(lean_object* v_linterOption_435_, lean_object* v_stx_436_, lean_object* v_msg_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_name_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_459_; 
v_name_441_ = lean_ctor_get(v_linterOption_435_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_linterOption_435_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v_linterOption_435_, 1);
lean_dec(v_unused_460_);
v___x_443_ = v_linterOption_435_;
v_isShared_444_ = v_isSharedCheck_459_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_name_441_);
lean_dec(v_linterOption_435_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_459_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_445_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1);
lean_inc(v_name_441_);
v___x_446_ = l_Lean_MessageData_ofName(v_name_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set_tag(v___x_443_, 7);
lean_ctor_set(v___x_443_, 1, v___x_446_);
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_448_ = v___x_443_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_458_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_disable_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_449_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3);
v___x_450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_448_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v_disable_451_ = l_Lean_MessageData_note(v___x_450_);
v___x_452_ = l_Lean_Linter_linterMessageTag;
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v_msg_437_);
lean_ctor_set(v___x_453_, 1, v_disable_451_);
v___x_454_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_455_, 0, v_name_441_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
lean_inc(v_stx_436_);
v___x_456_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_456_, 0, v_stx_436_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(v_stx_436_, v___x_456_, v___y_438_, v___y_439_);
lean_dec(v_stx_436_);
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___boxed(lean_object* v_linterOption_461_, lean_object* v_stx_462_, lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v_linterOption_461_, v_stx_462_, v_msg_463_, v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_467_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__0));
v___x_470_ = l_Lean_stringToMessageData(v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(lean_object* v___x_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
if (lean_obj_tag(v_a_472_) == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v_a_473_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
else
{
lean_object* v_key_479_; lean_object* v_value_480_; lean_object* v_tail_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_key_479_ = lean_ctor_get(v_a_472_, 0);
lean_inc(v_key_479_);
v_value_480_ = lean_ctor_get(v_a_472_, 1);
lean_inc(v_value_480_);
v_tail_481_ = lean_ctor_get(v_a_472_, 2);
lean_inc(v_tail_481_);
lean_dec_ref_known(v_a_472_, 3);
v___x_482_ = lean_box(0);
v___x_483_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(v___x_471_, v_value_480_);
if (v___x_483_ == 0)
{
uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_484_ = 1;
v___x_485_ = l_Lean_Linter_linter_fmt_missing;
v___x_486_ = l_Lean_Syntax_ofRange(v_key_479_, v___x_484_);
v___x_487_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1);
v___x_488_ = lean_box(0);
v___x_489_ = l_Lean_Expr_const___override(v_value_480_, v___x_488_);
v___x_490_ = l_Lean_MessageData_ofExpr(v___x_489_);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_487_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___x_485_, v___x_486_, v___x_491_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_dec_ref_known(v___x_492_, 1);
v_a_472_ = v_tail_481_;
v_a_473_ = v___x_482_;
goto _start;
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_tail_481_);
v_a_494_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_492_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_492_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_dec(v_value_480_);
lean_dec(v_key_479_);
v_a_472_ = v_tail_481_;
v_a_473_ = v___x_482_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___boxed(lean_object* v___x_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(v___x_503_, v_a_504_, v_a_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v___x_503_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(lean_object* v___x_510_, lean_object* v_as_511_, size_t v_sz_512_, size_t v_i_513_, lean_object* v_b_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = lean_usize_dec_lt(v_i_513_, v_sz_512_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v_b_514_);
return v___x_519_;
}
else
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_array_uget_borrowed(v_as_511_, v_i_513_);
lean_inc(v_a_520_);
v___x_521_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(v___x_510_, v_a_520_, v_b_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_534_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_534_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
if (lean_obj_tag(v_a_522_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; 
v_a_526_ = lean_ctor_get(v_a_522_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v_a_522_, 1);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v_a_526_);
v___x_528_ = v___x_524_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
else
{
lean_object* v_a_530_; size_t v___x_531_; size_t v___x_532_; 
lean_del_object(v___x_524_);
v_a_530_ = lean_ctor_get(v_a_522_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v_a_522_, 1);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_513_, v___x_531_);
v_i_513_ = v___x_532_;
v_b_514_ = v_a_530_;
goto _start;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_a_535_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_521_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_521_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4___boxed(lean_object* v___x_543_, lean_object* v_as_544_, lean_object* v_sz_545_, lean_object* v_i_546_, lean_object* v_b_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_545_);
lean_dec(v_sz_545_);
v_i_boxed_552_ = lean_unbox_usize(v_i_546_);
lean_dec(v_i_546_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(v___x_543_, v_as_544_, v_sz_boxed_551_, v_i_boxed_552_, v_b_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec_ref(v_as_544_);
lean_dec_ref(v___x_543_);
return v_res_553_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0));
v___x_556_ = l_Lean_stringToMessageData(v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__2));
v___x_559_ = l_Lean_stringToMessageData(v___x_558_);
return v___x_559_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__4));
v___x_562_ = l_Lean_stringToMessageData(v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__6));
v___x_565_ = l_Lean_stringToMessageData(v___x_564_);
return v___x_565_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__8));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(lean_object* v___x_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
if (lean_obj_tag(v_a_572_) == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_577_, 0, v_a_573_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
else
{
lean_object* v_value_579_; lean_object* v_key_580_; lean_object* v_tail_581_; lean_object* v_stx_582_; lean_object* v_formatterName_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_635_; 
v_value_579_ = lean_ctor_get(v_a_572_, 1);
lean_inc(v_value_579_);
v_key_580_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_key_580_);
v_tail_581_ = lean_ctor_get(v_a_572_, 2);
lean_inc(v_tail_581_);
lean_dec_ref_known(v_a_572_, 3);
v_stx_582_ = lean_ctor_get(v_value_579_, 0);
v_formatterName_583_ = lean_ctor_get(v_value_579_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_value_579_);
if (v_isSharedCheck_635_ == 0)
{
v___x_585_ = v_value_579_;
v_isShared_586_ = v_isSharedCheck_635_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_formatterName_583_);
lean_inc(v_stx_582_);
lean_dec(v_value_579_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_635_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_587_ = lean_box(0);
lean_inc(v_stx_582_);
v___x_588_ = l_Lean_Syntax_getKind(v_stx_582_);
v___x_589_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(v___x_571_, v___x_588_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; lean_object* v___y_592_; uint8_t v___x_627_; 
v___x_590_ = 1;
v___x_627_ = l_Lean_Name_isAnonymous(v_formatterName_583_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_628_ = lean_box(0);
v___x_629_ = l_Lean_Expr_const___override(v_formatterName_583_, v___x_628_);
v___x_630_ = l_Lean_MessageData_ofExpr(v___x_629_);
v___x_631_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___y_592_ = v___x_632_;
goto v___jp_591_;
}
else
{
lean_object* v___x_633_; 
lean_dec(v_formatterName_583_);
v___x_633_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10);
v___y_592_ = v___x_633_;
goto v___jp_591_;
}
v___jp_591_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_593_ = l_Lean_Linter_linter_fmt_missing;
v___x_594_ = l_Lean_Syntax_ofRange(v_key_580_, v___x_590_);
v___x_595_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1);
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 7);
lean_ctor_set(v___x_585_, 1, v___y_592_);
lean_ctor_set(v___x_585_, 0, v___x_595_);
v___x_597_ = v___x_585_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___y_592_);
v___x_597_ = v_reuseFailAlloc_626_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_598_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_box(0);
v___x_601_ = l_Lean_Expr_const___override(v___x_588_, v___x_600_);
v___x_602_ = l_Lean_MessageData_ofExpr(v___x_601_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_599_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_box(0);
v___x_609_ = l_Lean_Syntax_formatStx(v_stx_582_, v___x_608_, v___x_589_);
v___x_610_ = l_Std_Format_defWidth;
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l_Std_Format_pretty(v___x_609_, v___x_610_, v___x_611_, v___x_611_);
v___x_613_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
v___x_614_ = l_Lean_MessageData_ofFormat(v___x_613_);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_607_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___x_593_, v___x_594_, v___x_615_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_dec_ref_known(v___x_616_, 1);
v_a_572_ = v_tail_581_;
v_a_573_ = v___x_587_;
goto _start;
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_dec(v_tail_581_);
v_a_618_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_616_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
else
{
lean_dec(v___x_588_);
lean_del_object(v___x_585_);
lean_dec(v_formatterName_583_);
lean_dec(v_stx_582_);
lean_dec(v_key_580_);
v_a_572_ = v_tail_581_;
v_a_573_ = v___x_587_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___boxed(lean_object* v___x_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(v___x_636_, v_a_637_, v_a_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec_ref(v___x_636_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(lean_object* v___x_643_, lean_object* v_as_644_, size_t v_sz_645_, size_t v_i_646_, lean_object* v_b_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
uint8_t v___x_651_; 
v___x_651_ = lean_usize_dec_lt(v_i_646_, v_sz_645_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v_b_647_);
return v___x_652_;
}
else
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_array_uget_borrowed(v_as_644_, v_i_646_);
lean_inc(v_a_653_);
v___x_654_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(v___x_643_, v_a_653_, v_b_647_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_667_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_667_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_667_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_667_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
if (lean_obj_tag(v_a_655_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v_a_655_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v_a_655_, 1);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v_a_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v_a_663_; size_t v___x_664_; size_t v___x_665_; 
lean_del_object(v___x_657_);
v_a_663_ = lean_ctor_get(v_a_655_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v_a_655_, 1);
v___x_664_ = ((size_t)1ULL);
v___x_665_ = lean_usize_add(v_i_646_, v___x_664_);
v_i_646_ = v___x_665_;
v_b_647_ = v_a_663_;
goto _start;
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v_a_668_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_654_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_654_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5___boxed(lean_object* v___x_676_, lean_object* v_as_677_, lean_object* v_sz_678_, lean_object* v_i_679_, lean_object* v_b_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
size_t v_sz_boxed_684_; size_t v_i_boxed_685_; lean_object* v_res_686_; 
v_sz_boxed_684_ = lean_unbox_usize(v_sz_678_);
lean_dec(v_sz_678_);
v_i_boxed_685_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(v___x_676_, v_as_677_, v_sz_boxed_684_, v_i_boxed_685_, v_b_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec_ref(v_as_677_);
lean_dec_ref(v___x_676_);
return v_res_686_;
}
}
static lean_object* _init_l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(lean_object* v_stx_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_695_; lean_object* v_env_696_; lean_object* v_fileMap_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_scopes_700_; lean_object* v___x_701_; lean_object* v_opts_702_; lean_object* v___x_703_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v_infoState_722_; lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_695_ = lean_st_ref_get(v_a_693_);
v_env_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_env_696_);
lean_dec(v___x_695_);
v_fileMap_697_ = lean_ctor_get(v_a_692_, 1);
v___x_698_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_699_ = lean_st_ref_get(v_a_693_);
v_scopes_700_ = lean_ctor_get(v___x_699_, 2);
lean_inc(v_scopes_700_);
lean_dec(v___x_699_);
v___x_701_ = l_List_head_x21___redArg(v___x_698_, v_scopes_700_);
lean_dec(v_scopes_700_);
v_opts_702_ = lean_ctor_get(v___x_701_, 1);
lean_inc_ref_n(v_opts_702_, 2);
lean_dec(v___x_701_);
v___x_703_ = lean_st_ref_get(v_a_693_);
v_infoState_722_ = lean_ctor_get(v___x_703_, 8);
lean_inc_ref(v_infoState_722_);
lean_dec(v___x_703_);
v___f_723_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__0), 2, 1);
lean_closure_set(v___f_723_, 0, v_infoState_722_);
v___x_724_ = lean_mk_thunk(v___f_723_);
v___f_725_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1___boxed), 2, 1);
lean_closure_set(v___f_725_, 0, v___x_724_);
lean_inc_n(v_stx_691_, 2);
v___x_726_ = l_Lean_Fmt_collectSyntaxLineInfos(v_stx_691_);
lean_inc_ref(v_fileMap_697_);
v___x_727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_727_, 0, v_env_696_);
lean_ctor_set(v___x_727_, 1, v_fileMap_697_);
lean_ctor_set(v___x_727_, 2, v___f_725_);
lean_ctor_set(v___x_727_, 3, v_opts_702_);
lean_ctor_set(v___x_727_, 4, v___x_726_);
v___x_728_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 1);
lean_closure_set(v___x_728_, 0, v_stx_691_);
v___x_729_ = l_Lean_FmtM_run___redArg(v___x_727_, v___x_728_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___y_732_; lean_object* v___x_743_; 
lean_dec_ref(v_opts_702_);
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc_n(v_a_730_, 2);
lean_dec_ref_known(v___x_729_, 1);
v___x_743_ = l_Lean_Fmt_Error_ref_x3f(v_a_730_);
if (lean_obj_tag(v___x_743_) == 0)
{
v___y_732_ = v_stx_691_;
goto v___jp_731_;
}
else
{
lean_object* v_val_744_; 
lean_dec(v_stx_691_);
v_val_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_743_, 1);
v___y_732_ = v_val_744_;
goto v___jp_731_;
}
v___jp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = l_Lean_Linter_linter_fmt_missing;
v___x_734_ = lean_obj_once(&l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1, &l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1_once, _init_l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1);
switch(lean_obj_tag(v_a_730_))
{
case 0:
{
lean_object* v___x_735_; 
lean_dec_ref_known(v_a_730_, 0);
v___x_735_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__2));
v___y_705_ = v___x_733_;
v___y_706_ = v___x_734_;
v___y_707_ = v___y_732_;
v___y_708_ = v___x_735_;
goto v___jp_704_;
}
case 1:
{
lean_object* v_err_736_; 
v_err_736_ = lean_ctor_get(v_a_730_, 0);
lean_inc_ref(v_err_736_);
lean_dec_ref_known(v_a_730_, 1);
if (lean_obj_tag(v_err_736_) == 0)
{
lean_object* v_msg_737_; 
v_msg_737_ = lean_ctor_get(v_err_736_, 0);
lean_inc_ref(v_msg_737_);
lean_dec_ref_known(v_err_736_, 1);
v___y_705_ = v___x_733_;
v___y_706_ = v___x_734_;
v___y_707_ = v___y_732_;
v___y_708_ = v_msg_737_;
goto v___jp_704_;
}
else
{
lean_object* v_msg_738_; 
v_msg_738_ = lean_ctor_get(v_err_736_, 1);
lean_inc_ref(v_msg_738_);
lean_dec_ref(v_err_736_);
v___y_705_ = v___x_733_;
v___y_706_ = v___x_734_;
v___y_707_ = v___y_732_;
v___y_708_ = v_msg_738_;
goto v___jp_704_;
}
}
case 2:
{
lean_object* v_err_739_; lean_object* v_msg_740_; 
v_err_739_ = lean_ctor_get(v_a_730_, 0);
lean_inc_ref(v_err_739_);
lean_dec_ref_known(v_a_730_, 1);
v_msg_740_ = lean_ctor_get(v_err_739_, 2);
lean_inc_ref(v_msg_740_);
lean_dec_ref(v_err_739_);
v___y_705_ = v___x_733_;
v___y_706_ = v___x_734_;
v___y_707_ = v___y_732_;
v___y_708_ = v_msg_740_;
goto v___jp_704_;
}
default: 
{
lean_object* v_err_741_; lean_object* v_msg_742_; 
v_err_741_ = lean_ctor_get(v_a_730_, 0);
lean_inc_ref(v_err_741_);
lean_dec_ref_known(v_a_730_, 1);
v_msg_742_ = lean_ctor_get(v_err_741_, 1);
lean_inc_ref(v_msg_742_);
lean_dec_ref(v_err_741_);
v___y_705_ = v___x_733_;
v___y_706_ = v___x_734_;
v___y_707_ = v___y_732_;
v___y_708_ = v_msg_742_;
goto v___jp_704_;
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v_toState_746_; lean_object* v_missingFormatters_747_; lean_object* v_partialFormatters_748_; lean_object* v_buckets_749_; lean_object* v___x_750_; size_t v_sz_751_; size_t v___x_752_; lean_object* v___x_753_; 
lean_dec(v_stx_691_);
v_a_745_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_729_, 1);
v_toState_746_ = lean_ctor_get(v_a_745_, 0);
lean_inc_ref(v_toState_746_);
lean_dec(v_a_745_);
v_missingFormatters_747_ = lean_ctor_get(v_toState_746_, 3);
lean_inc_ref(v_missingFormatters_747_);
v_partialFormatters_748_ = lean_ctor_get(v_toState_746_, 4);
lean_inc_ref(v_partialFormatters_748_);
lean_dec_ref(v_toState_746_);
v_buckets_749_ = lean_ctor_get(v_missingFormatters_747_, 1);
lean_inc_ref(v_buckets_749_);
lean_dec_ref(v_missingFormatters_747_);
v___x_750_ = lean_box(0);
v_sz_751_ = lean_array_size(v_buckets_749_);
v___x_752_ = ((size_t)0ULL);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(v_opts_702_, v_buckets_749_, v_sz_751_, v___x_752_, v___x_750_, v_a_692_, v_a_693_);
lean_dec_ref(v_buckets_749_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_buckets_754_; size_t v_sz_755_; lean_object* v___x_756_; 
lean_dec_ref_known(v___x_753_, 1);
v_buckets_754_ = lean_ctor_get(v_partialFormatters_748_, 1);
lean_inc_ref(v_buckets_754_);
lean_dec_ref(v_partialFormatters_748_);
v_sz_755_ = lean_array_size(v_buckets_754_);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(v_opts_702_, v_buckets_754_, v_sz_755_, v___x_752_, v___x_750_, v_a_692_, v_a_693_);
lean_dec_ref(v_buckets_754_);
lean_dec_ref(v_opts_702_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_756_, 0);
lean_dec(v_unused_764_);
v___x_758_ = v___x_756_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_dec(v___x_756_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_750_);
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_750_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
else
{
return v___x_756_;
}
}
else
{
lean_dec_ref(v_partialFormatters_748_);
lean_dec_ref(v_opts_702_);
return v___x_753_;
}
}
v___jp_704_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_709_, 0, v___y_708_);
v___x_710_ = l_Lean_MessageData_ofFormat(v___x_709_);
lean_inc_ref(v___y_706_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___y_706_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
lean_inc_ref(v___y_705_);
v___x_712_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___y_705_, v___y_707_, v___x_711_, v_a_692_, v_a_693_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_720_; 
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v___x_712_, 0);
lean_dec(v_unused_721_);
v___x_714_ = v___x_712_;
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
else
{
lean_dec(v___x_712_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_720_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_box(0);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
else
{
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___boxed(lean_object* v_stx_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(v_stx_765_, v_a_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10(lean_object* v_msgData_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v_msgData_770_, v___y_772_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_msgData_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10(v_msgData_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(lean_object* v_o_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_env_785_; lean_object* v___x_786_; lean_object* v_toEnvExtension_787_; lean_object* v_asyncMode_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v_merged_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v___x_783_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_784_ = lean_st_ref_get(v___y_781_);
v_env_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc_ref(v_env_785_);
lean_dec(v___x_784_);
v___x_786_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_787_ = lean_ctor_get(v___x_786_, 0);
v_asyncMode_788_ = lean_ctor_get(v_toEnvExtension_787_, 2);
v___x_789_ = lean_box(0);
v___x_790_ = 0;
v___x_791_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_783_, v___x_786_, v_env_785_, v_asyncMode_788_, v___x_789_, v___x_790_);
v_merged_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_791_, 1);
lean_dec(v_unused_801_);
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_merged_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v_merged_792_);
lean_ctor_set(v___x_794_, 0, v_o_780_);
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_o_780_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_merged_792_);
v___x_797_ = v_reuseFailAlloc_799_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; 
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg___boxed(lean_object* v_o_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_o_802_, v___y_803_);
lean_dec(v___y_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_scopes_811_; lean_object* v___x_812_; lean_object* v_opts_813_; lean_object* v___x_814_; 
v___x_809_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_810_ = lean_st_ref_get(v___y_807_);
v_scopes_811_ = lean_ctor_get(v___x_810_, 2);
lean_inc(v_scopes_811_);
lean_dec(v___x_810_);
v___x_812_ = l_List_head_x21___redArg(v___x_809_, v_scopes_811_);
lean_dec(v_scopes_811_);
v_opts_813_ = lean_ctor_get(v___x_812_, 1);
lean_inc_ref(v_opts_813_);
lean_dec(v___x_812_);
v___x_814_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_opts_813_, v___y_807_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0___boxed(lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0(lean_object* v_cmdStx_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_841_; 
v___x_823_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(v___y_820_, v___y_821_);
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_841_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_841_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_841_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_toOptions_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_toOptions_828_ = lean_ctor_get(v_a_824_, 0);
lean_inc_ref(v_toOptions_828_);
lean_dec(v_a_824_);
v___x_829_ = l_Lean_Linter_linter_fmt_missing;
v___x_830_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_toOptions_828_, v___x_829_);
lean_dec_ref(v_toOptions_828_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_833_; 
lean_dec(v_cmdStx_819_);
v___x_831_ = lean_box(0);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_831_);
v___x_833_ = v___x_826_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
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
uint8_t v___x_835_; 
v___x_835_ = l_Lean_Syntax_hasMissing(v_cmdStx_819_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_del_object(v___x_826_);
v___x_836_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(v_cmdStx_819_, v___y_820_, v___y_821_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_dec(v_cmdStx_819_);
v___x_837_ = lean_box(0);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_837_);
v___x_839_ = v___x_826_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0___boxed(lean_object* v_cmdStx_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Linter_fmtMissing___lam__0(v_cmdStx_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0(lean_object* v_o_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_o_857_, v___y_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___boxed(lean_object* v_o_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0(v_o_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l_Lean_Linter_fmtMissing));
v___x_869_ = l_Lean_Elab_Command_addLinter(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2____boxed(lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_();
return v_res_871_;
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
