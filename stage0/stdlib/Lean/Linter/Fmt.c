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
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_229_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_230_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__1);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_232_, 11, v___x_229_);
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
lean_object* v___x_249_; lean_object* v_env_250_; uint8_t v___x_251_; lean_object* v_env_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_scopes_255_; lean_object* v___x_256_; lean_object* v_opts_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_249_ = lean_st_ref_get(v___y_247_);
v_env_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_env_250_);
lean_dec(v___x_249_);
v___x_251_ = 0;
v_env_252_ = l_Lean_Environment_setRecordingDeps(v_env_250_, v___x_251_);
v___x_253_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_254_ = lean_st_ref_get(v___y_247_);
v_scopes_255_ = lean_ctor_get(v___x_254_, 2);
lean_inc(v_scopes_255_);
lean_dec(v___x_254_);
v___x_256_ = l_List_head_x21___redArg(v___x_253_, v_scopes_255_);
lean_dec(v_scopes_255_);
v_opts_257_ = lean_ctor_get(v___x_256_, 1);
lean_inc_ref(v_opts_257_);
lean_dec(v___x_256_);
v___x_258_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__2);
v___x_259_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___closed__5);
v___x_260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_260_, 0, v_env_252_);
lean_ctor_set(v___x_260_, 1, v___x_258_);
lean_ctor_set(v___x_260_, 2, v___x_259_);
lean_ctor_set(v___x_260_, 3, v_opts_257_);
v___x_261_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_msgData_246_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_msgData_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v_msgData_263_, v___y_264_);
lean_dec(v___y_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(lean_object* v_ref_268_, lean_object* v_msgData_269_, uint8_t v_severity_270_, uint8_t v_isSilent_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
uint8_t v___y_276_; uint8_t v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; uint8_t v___y_341_; uint8_t v___y_342_; lean_object* v___y_343_; lean_object* v___y_344_; uint8_t v___y_367_; uint8_t v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; uint8_t v___y_374_; uint8_t v___y_375_; uint8_t v___x_390_; uint8_t v___y_392_; uint8_t v___x_402_; 
v___x_390_ = 2;
v___x_402_ = l_Lean_instBEqMessageSeverity_beq(v_severity_270_, v___x_390_);
if (v___x_402_ == 0)
{
v___y_392_ = v___x_402_;
goto v___jp_391_;
}
else
{
uint8_t v___x_403_; 
lean_inc_ref(v_msgData_269_);
v___x_403_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_269_);
if (v___x_403_ == 0)
{
v___y_392_ = v___x_403_;
goto v___jp_391_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref(v_msgData_269_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
v___jp_275_:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Elab_Command_getScope___redArg(v___y_283_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v_currNamespace_286_; lean_object* v___x_287_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_284_, 1);
v_currNamespace_286_ = lean_ctor_get(v_a_285_, 2);
lean_inc(v_currNamespace_286_);
lean_dec(v_a_285_);
v___x_287_ = l_Lean_Elab_Command_getScope___redArg(v___y_283_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_323_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_323_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_323_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_323_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_openDecls_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v_env_297_; lean_object* v_messages_298_; lean_object* v_scopes_299_; lean_object* v_usedQuotCtxts_300_; lean_object* v_nextMacroScope_301_; lean_object* v_maxRecDepth_302_; lean_object* v_ngen_303_; lean_object* v_auxDeclNGen_304_; lean_object* v_infoState_305_; lean_object* v_traceState_306_; lean_object* v_snapshotTasks_307_; lean_object* v_prevLinterStates_308_; lean_object* v_codeQualityEntryTasks_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_322_; 
v_openDecls_292_ = lean_ctor_get(v_a_288_, 3);
lean_inc(v_openDecls_292_);
lean_dec(v_a_288_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_currNamespace_286_);
lean_ctor_set(v___x_293_, 1, v_openDecls_292_);
v___x_294_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v___y_281_);
lean_inc_ref(v___y_280_);
lean_inc_ref(v___y_279_);
v___x_295_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_295_, 0, v___y_279_);
lean_ctor_set(v___x_295_, 1, v___y_282_);
lean_ctor_set(v___x_295_, 2, v___y_278_);
lean_ctor_set(v___x_295_, 3, v___y_280_);
lean_ctor_set(v___x_295_, 4, v___x_294_);
lean_ctor_set_uint8(v___x_295_, sizeof(void*)*5, v___y_277_);
lean_ctor_set_uint8(v___x_295_, sizeof(void*)*5 + 1, v___y_276_);
lean_ctor_set_uint8(v___x_295_, sizeof(void*)*5 + 2, v_isSilent_271_);
v___x_296_ = lean_st_ref_take(v___y_283_);
v_env_297_ = lean_ctor_get(v___x_296_, 0);
v_messages_298_ = lean_ctor_get(v___x_296_, 1);
v_scopes_299_ = lean_ctor_get(v___x_296_, 2);
v_usedQuotCtxts_300_ = lean_ctor_get(v___x_296_, 3);
v_nextMacroScope_301_ = lean_ctor_get(v___x_296_, 4);
v_maxRecDepth_302_ = lean_ctor_get(v___x_296_, 5);
v_ngen_303_ = lean_ctor_get(v___x_296_, 6);
v_auxDeclNGen_304_ = lean_ctor_get(v___x_296_, 7);
v_infoState_305_ = lean_ctor_get(v___x_296_, 8);
v_traceState_306_ = lean_ctor_get(v___x_296_, 9);
v_snapshotTasks_307_ = lean_ctor_get(v___x_296_, 10);
v_prevLinterStates_308_ = lean_ctor_get(v___x_296_, 11);
v_codeQualityEntryTasks_309_ = lean_ctor_get(v___x_296_, 12);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_322_ == 0)
{
v___x_311_ = v___x_296_;
v_isShared_312_ = v_isSharedCheck_322_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_codeQualityEntryTasks_309_);
lean_inc(v_prevLinterStates_308_);
lean_inc(v_snapshotTasks_307_);
lean_inc(v_traceState_306_);
lean_inc(v_infoState_305_);
lean_inc(v_auxDeclNGen_304_);
lean_inc(v_ngen_303_);
lean_inc(v_maxRecDepth_302_);
lean_inc(v_nextMacroScope_301_);
lean_inc(v_usedQuotCtxts_300_);
lean_inc(v_scopes_299_);
lean_inc(v_messages_298_);
lean_inc(v_env_297_);
lean_dec(v___x_296_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_322_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = lean_box(0);
v___x_314_ = l_Lean_MessageLog_add(v___x_295_, v_messages_298_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_314_);
v___x_316_ = v___x_311_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_env_297_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_321_, 2, v_scopes_299_);
lean_ctor_set(v_reuseFailAlloc_321_, 3, v_usedQuotCtxts_300_);
lean_ctor_set(v_reuseFailAlloc_321_, 4, v_nextMacroScope_301_);
lean_ctor_set(v_reuseFailAlloc_321_, 5, v_maxRecDepth_302_);
lean_ctor_set(v_reuseFailAlloc_321_, 6, v_ngen_303_);
lean_ctor_set(v_reuseFailAlloc_321_, 7, v_auxDeclNGen_304_);
lean_ctor_set(v_reuseFailAlloc_321_, 8, v_infoState_305_);
lean_ctor_set(v_reuseFailAlloc_321_, 9, v_traceState_306_);
lean_ctor_set(v_reuseFailAlloc_321_, 10, v_snapshotTasks_307_);
lean_ctor_set(v_reuseFailAlloc_321_, 11, v_prevLinterStates_308_);
lean_ctor_set(v_reuseFailAlloc_321_, 12, v_codeQualityEntryTasks_309_);
v___x_316_ = v_reuseFailAlloc_321_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_st_ref_put(v___y_283_, v___x_316_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_313_);
v___x_319_ = v___x_290_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_313_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_currNamespace_286_);
lean_dec_ref(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_278_);
v_a_324_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_287_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_287_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec_ref(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_278_);
v_a_332_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_284_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_284_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
v___jp_340_:
{
lean_object* v_fileName_345_; lean_object* v_fileMap_346_; uint8_t v_suppressElabErrors_347_; lean_object* v___x_348_; lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_365_; 
v_fileName_345_ = lean_ctor_get(v___y_272_, 0);
v_fileMap_346_ = lean_ctor_get(v___y_272_, 1);
v_suppressElabErrors_347_ = lean_ctor_get_uint8(v___y_272_, sizeof(void*)*10);
v___x_348_ = lean_box(v_suppressElabErrors_347_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_349_, 0, v___x_348_);
v___x_350_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_269_);
v___x_351_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v___x_350_, v___y_273_);
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
lean_inc_ref_n(v_fileMap_346_, 2);
v___x_356_ = l_Lean_FileMap_toPosition(v_fileMap_346_, v___y_343_);
lean_dec(v___y_343_);
v___x_357_ = l_Lean_FileMap_toPosition(v_fileMap_346_, v___y_344_);
lean_dec(v___y_344_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
v___x_359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0));
if (v_suppressElabErrors_347_ == 0)
{
lean_del_object(v___x_354_);
lean_dec_ref(v___f_349_);
v___y_276_ = v___y_341_;
v___y_277_ = v___y_342_;
v___y_278_ = v___x_358_;
v___y_279_ = v_fileName_345_;
v___y_280_ = v___x_359_;
v___y_281_ = v_a_352_;
v___y_282_ = v___x_356_;
v___y_283_ = v___y_273_;
goto v___jp_275_;
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
v___y_276_ = v___y_341_;
v___y_277_ = v___y_342_;
v___y_278_ = v___x_358_;
v___y_279_ = v_fileName_345_;
v___y_280_ = v___x_359_;
v___y_281_ = v_a_352_;
v___y_282_ = v___x_356_;
v___y_283_ = v___y_273_;
goto v___jp_275_;
}
}
}
}
v___jp_366_:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Syntax_getTailPos_x3f(v___y_369_, v___y_368_);
lean_dec(v___y_369_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_inc(v___y_370_);
v___y_341_ = v___y_367_;
v___y_342_ = v___y_368_;
v___y_343_ = v___y_370_;
v___y_344_ = v___y_370_;
goto v___jp_340_;
}
else
{
lean_object* v_val_372_; 
v_val_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_val_372_);
lean_dec_ref_known(v___x_371_, 1);
v___y_341_ = v___y_367_;
v___y_342_ = v___y_368_;
v___y_343_ = v___y_370_;
v___y_344_ = v_val_372_;
goto v___jp_340_;
}
}
v___jp_373_:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Elab_Command_getRef___redArg(v___y_272_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v_ref_378_; lean_object* v___x_379_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
v_ref_378_ = l_Lean_replaceRef(v_ref_268_, v_a_377_);
lean_dec(v_a_377_);
v___x_379_ = l_Lean_Syntax_getPos_x3f(v_ref_378_, v___y_374_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v___y_367_ = v___y_375_;
v___y_368_ = v___y_374_;
v___y_369_ = v_ref_378_;
v___y_370_ = v___x_380_;
goto v___jp_366_;
}
else
{
lean_object* v_val_381_; 
v_val_381_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_val_381_);
lean_dec_ref_known(v___x_379_, 1);
v___y_367_ = v___y_375_;
v___y_368_ = v___y_374_;
v___y_369_ = v_ref_378_;
v___y_370_ = v_val_381_;
goto v___jp_366_;
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec_ref(v_msgData_269_);
v_a_382_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_376_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_376_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_scopes_395_; lean_object* v___x_396_; lean_object* v_opts_397_; uint8_t v___x_398_; uint8_t v___x_399_; 
v___x_393_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_394_ = lean_st_ref_get(v___y_273_);
v_scopes_395_ = lean_ctor_get(v___x_394_, 2);
lean_inc(v_scopes_395_);
lean_dec(v___x_394_);
v___x_396_ = l_List_head_x21___redArg(v___x_393_, v_scopes_395_);
lean_dec(v_scopes_395_);
v_opts_397_ = lean_ctor_get(v___x_396_, 1);
lean_inc_ref(v_opts_397_);
lean_dec(v___x_396_);
v___x_398_ = 1;
v___x_399_ = l_Lean_instBEqMessageSeverity_beq(v_severity_270_, v___x_398_);
if (v___x_399_ == 0)
{
lean_dec_ref(v_opts_397_);
v___y_374_ = v___y_392_;
v___y_375_ = v_severity_270_;
goto v___jp_373_;
}
else
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = l_Lean_warningAsError;
v___x_401_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_opts_397_, v___x_400_);
lean_dec_ref(v_opts_397_);
if (v___x_401_ == 0)
{
v___y_374_ = v___y_392_;
v___y_375_ = v_severity_270_;
goto v___jp_373_;
}
else
{
v___y_374_ = v___y_392_;
v___y_375_ = v___x_390_;
goto v___jp_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___boxed(lean_object* v_ref_406_, lean_object* v_msgData_407_, lean_object* v_severity_408_, lean_object* v_isSilent_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
uint8_t v_severity_boxed_413_; uint8_t v_isSilent_boxed_414_; lean_object* v_res_415_; 
v_severity_boxed_413_ = lean_unbox(v_severity_408_);
v_isSilent_boxed_414_ = lean_unbox(v_isSilent_409_);
v_res_415_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(v_ref_406_, v_msgData_407_, v_severity_boxed_413_, v_isSilent_boxed_414_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v_ref_406_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(lean_object* v_ref_416_, lean_object* v_msgData_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
uint8_t v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; 
v___x_421_ = 1;
v___x_422_ = 0;
v___x_423_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5(v_ref_416_, v_msgData_417_, v___x_421_, v___x_422_, v___y_418_, v___y_419_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3___boxed(lean_object* v_ref_424_, lean_object* v_msgData_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(v_ref_424_, v_msgData_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v_ref_424_);
return v_res_429_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__0));
v___x_432_ = l_Lean_stringToMessageData(v___x_431_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__2));
v___x_435_ = l_Lean_stringToMessageData(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(lean_object* v_linterOption_436_, lean_object* v_stx_437_, lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_name_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_460_; 
v_name_442_ = lean_ctor_get(v_linterOption_436_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v_linterOption_436_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v_linterOption_436_, 1);
lean_dec(v_unused_461_);
v___x_444_ = v_linterOption_436_;
v_isShared_445_ = v_isSharedCheck_460_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_name_442_);
lean_dec(v_linterOption_436_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_460_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_446_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__1);
lean_inc(v_name_442_);
v___x_447_ = l_Lean_MessageData_ofName(v_name_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 7);
lean_ctor_set(v___x_444_, 1, v___x_447_);
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_449_ = v___x_444_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_459_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_disable_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_450_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___closed__3);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v_disable_452_ = l_Lean_MessageData_note(v___x_451_);
v___x_453_ = l_Lean_Linter_linterMessageTag;
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v_msg_438_);
lean_ctor_set(v___x_454_, 1, v_disable_452_);
v___x_455_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_456_, 0, v_name_442_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
lean_inc(v_stx_437_);
v___x_457_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_457_, 0, v_stx_437_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3(v_stx_437_, v___x_457_, v___y_439_, v___y_440_);
lean_dec(v_stx_437_);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1___boxed(lean_object* v_linterOption_462_, lean_object* v_stx_463_, lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v_linterOption_462_, v_stx_463_, v_msg_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_468_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__0));
v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(lean_object* v___x_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
if (lean_obj_tag(v_a_473_) == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_a_474_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v_key_480_; lean_object* v_value_481_; lean_object* v_tail_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_key_480_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_key_480_);
v_value_481_ = lean_ctor_get(v_a_473_, 1);
lean_inc(v_value_481_);
v_tail_482_ = lean_ctor_get(v_a_473_, 2);
lean_inc(v_tail_482_);
lean_dec_ref_known(v_a_473_, 3);
v___x_483_ = lean_box(0);
v___x_484_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(v___x_472_, v_value_481_);
if (v___x_484_ == 0)
{
uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_485_ = 1;
v___x_486_ = l_Lean_Linter_linter_fmt_missing;
v___x_487_ = l_Lean_Syntax_ofRange(v_key_480_, v___x_485_);
v___x_488_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___closed__1);
v___x_489_ = lean_box(0);
v___x_490_ = l_Lean_Expr_const___override(v_value_481_, v___x_489_);
v___x_491_ = l_Lean_MessageData_ofExpr(v___x_490_);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_488_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___x_486_, v___x_487_, v___x_492_, v___y_475_, v___y_476_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_dec_ref_known(v___x_493_, 1);
v_a_473_ = v_tail_482_;
v_a_474_ = v___x_483_;
goto _start;
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v_tail_482_);
v_a_495_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_493_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_dec(v_value_481_);
lean_dec(v_key_480_);
v_a_473_ = v_tail_482_;
v_a_474_ = v___x_483_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3___boxed(lean_object* v___x_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(v___x_504_, v_a_505_, v_a_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec_ref(v___x_504_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(lean_object* v___x_511_, lean_object* v_as_512_, size_t v_sz_513_, size_t v_i_514_, lean_object* v_b_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = lean_usize_dec_lt(v_i_514_, v_sz_513_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v_b_515_);
return v___x_520_;
}
else
{
lean_object* v_a_521_; lean_object* v___x_522_; 
v_a_521_ = lean_array_uget_borrowed(v_as_512_, v_i_514_);
lean_inc(v_a_521_);
v___x_522_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__3(v___x_511_, v_a_521_, v_b_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_535_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_535_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_535_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_535_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
if (lean_obj_tag(v_a_523_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; 
v_a_527_ = lean_ctor_get(v_a_523_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v_a_523_, 1);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v_a_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
else
{
lean_object* v_a_531_; size_t v___x_532_; size_t v___x_533_; 
lean_del_object(v___x_525_);
v_a_531_ = lean_ctor_get(v_a_523_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v_a_523_, 1);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_514_, v___x_532_);
v_i_514_ = v___x_533_;
v_b_515_ = v_a_531_;
goto _start;
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
v_a_536_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_522_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_522_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4___boxed(lean_object* v___x_544_, lean_object* v_as_545_, lean_object* v_sz_546_, lean_object* v_i_547_, lean_object* v_b_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
size_t v_sz_boxed_552_; size_t v_i_boxed_553_; lean_object* v_res_554_; 
v_sz_boxed_552_ = lean_unbox_usize(v_sz_546_);
lean_dec(v_sz_546_);
v_i_boxed_553_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(v___x_544_, v_as_545_, v_sz_boxed_552_, v_i_boxed_553_, v_b_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec_ref(v_as_545_);
lean_dec_ref(v___x_544_);
return v_res_554_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__0));
v___x_557_ = l_Lean_stringToMessageData(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__2));
v___x_560_ = l_Lean_stringToMessageData(v___x_559_);
return v___x_560_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__4));
v___x_563_ = l_Lean_stringToMessageData(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__6));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__8));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5___closed__0));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(lean_object* v___x_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
if (lean_obj_tag(v_a_573_) == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_a_574_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v_value_580_; lean_object* v_key_581_; lean_object* v_tail_582_; lean_object* v_stx_583_; lean_object* v_formatterName_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_636_; 
v_value_580_ = lean_ctor_get(v_a_573_, 1);
lean_inc(v_value_580_);
v_key_581_ = lean_ctor_get(v_a_573_, 0);
lean_inc(v_key_581_);
v_tail_582_ = lean_ctor_get(v_a_573_, 2);
lean_inc(v_tail_582_);
lean_dec_ref_known(v_a_573_, 3);
v_stx_583_ = lean_ctor_get(v_value_580_, 0);
v_formatterName_584_ = lean_ctor_get(v_value_580_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_value_580_);
if (v_isSharedCheck_636_ == 0)
{
v___x_586_ = v_value_580_;
v_isShared_587_ = v_isSharedCheck_636_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_formatterName_584_);
lean_inc(v_stx_583_);
lean_dec(v_value_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_636_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_box(0);
lean_inc(v_stx_583_);
v___x_589_ = l_Lean_Syntax_getKind(v_stx_583_);
v___x_590_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind(v___x_572_, v___x_589_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; lean_object* v___y_593_; uint8_t v___x_628_; 
v___x_591_ = 1;
v___x_628_ = l_Lean_Name_isAnonymous(v_formatterName_584_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_629_ = lean_box(0);
v___x_630_ = l_Lean_Expr_const___override(v_formatterName_584_, v___x_629_);
v___x_631_ = l_Lean_MessageData_ofExpr(v___x_630_);
v___x_632_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__9);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___y_593_ = v___x_633_;
goto v___jp_592_;
}
else
{
lean_object* v___x_634_; 
lean_dec(v_formatterName_584_);
v___x_634_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__10);
v___y_593_ = v___x_634_;
goto v___jp_592_;
}
v___jp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_594_ = l_Lean_Linter_linter_fmt_missing;
v___x_595_ = l_Lean_Syntax_ofRange(v_key_581_, v___x_591_);
v___x_596_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__1);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 7);
lean_ctor_set(v___x_586_, 1, v___y_593_);
lean_ctor_set(v___x_586_, 0, v___x_596_);
v___x_598_ = v___x_586_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___y_593_);
v___x_598_ = v_reuseFailAlloc_627_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_599_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__3);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_box(0);
v___x_602_ = l_Lean_Expr_const___override(v___x_589_, v___x_601_);
v___x_603_ = l_Lean_MessageData_ofExpr(v___x_602_);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_600_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__5);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_obj_once(&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7, &l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7_once, _init_l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___closed__7);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_box(0);
v___x_610_ = l_Lean_Syntax_formatStx(v_stx_583_, v___x_609_, v___x_590_);
v___x_611_ = l_Std_Format_defWidth;
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = l_Std_Format_pretty(v___x_610_, v___x_611_, v___x_612_, v___x_612_);
v___x_614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___x_615_ = l_Lean_MessageData_ofFormat(v___x_614_);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_608_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___x_594_, v___x_595_, v___x_616_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_dec_ref_known(v___x_617_, 1);
v_a_573_ = v_tail_582_;
v_a_574_ = v___x_588_;
goto _start;
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_tail_582_);
v_a_619_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_617_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_617_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
}
else
{
lean_dec(v___x_589_);
lean_del_object(v___x_586_);
lean_dec(v_formatterName_584_);
lean_dec(v_stx_583_);
lean_dec(v_key_581_);
v_a_573_ = v_tail_582_;
v_a_574_ = v___x_588_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2___boxed(lean_object* v___x_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(v___x_637_, v_a_638_, v_a_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec_ref(v___x_637_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(lean_object* v___x_644_, lean_object* v_as_645_, size_t v_sz_646_, size_t v_i_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
uint8_t v___x_652_; 
v___x_652_ = lean_usize_dec_lt(v_i_647_, v_sz_646_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v_b_648_);
return v___x_653_;
}
else
{
lean_object* v_a_654_; lean_object* v___x_655_; 
v_a_654_ = lean_array_uget_borrowed(v_as_645_, v_i_647_);
lean_inc(v_a_654_);
v___x_655_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__2(v___x_644_, v_a_654_, v_b_648_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_668_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_668_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_668_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_668_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
if (lean_obj_tag(v_a_656_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; 
v_a_660_ = lean_ctor_get(v_a_656_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v_a_656_, 1);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_a_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
lean_object* v_a_664_; size_t v___x_665_; size_t v___x_666_; 
lean_del_object(v___x_658_);
v_a_664_ = lean_ctor_get(v_a_656_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v_a_656_, 1);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_647_, v___x_665_);
v_i_647_ = v___x_666_;
v_b_648_ = v_a_664_;
goto _start;
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
v_a_669_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_655_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_655_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5___boxed(lean_object* v___x_677_, lean_object* v_as_678_, lean_object* v_sz_679_, lean_object* v_i_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
size_t v_sz_boxed_685_; size_t v_i_boxed_686_; lean_object* v_res_687_; 
v_sz_boxed_685_ = lean_unbox_usize(v_sz_679_);
lean_dec(v_sz_679_);
v_i_boxed_686_ = lean_unbox_usize(v_i_680_);
lean_dec(v_i_680_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(v___x_677_, v_as_678_, v_sz_boxed_685_, v_i_boxed_686_, v_b_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec_ref(v_as_678_);
lean_dec_ref(v___x_677_);
return v_res_687_;
}
}
static lean_object* _init_l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__0));
v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(lean_object* v_stx_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v___x_696_; lean_object* v_env_697_; lean_object* v_fileMap_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_scopes_701_; lean_object* v___x_702_; lean_object* v_opts_703_; lean_object* v___x_704_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v_infoState_723_; lean_object* v___f_724_; lean_object* v___x_725_; lean_object* v___f_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_696_ = lean_st_ref_get(v_a_694_);
v_env_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc_ref(v_env_697_);
lean_dec(v___x_696_);
v_fileMap_698_ = lean_ctor_get(v_a_693_, 1);
v___x_699_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_700_ = lean_st_ref_get(v_a_694_);
v_scopes_701_ = lean_ctor_get(v___x_700_, 2);
lean_inc(v_scopes_701_);
lean_dec(v___x_700_);
v___x_702_ = l_List_head_x21___redArg(v___x_699_, v_scopes_701_);
lean_dec(v_scopes_701_);
v_opts_703_ = lean_ctor_get(v___x_702_, 1);
lean_inc_ref_n(v_opts_703_, 2);
lean_dec(v___x_702_);
v___x_704_ = lean_st_ref_get(v_a_694_);
v_infoState_723_ = lean_ctor_get(v___x_704_, 8);
lean_inc_ref(v_infoState_723_);
lean_dec(v___x_704_);
v___f_724_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__0), 2, 1);
lean_closure_set(v___f_724_, 0, v_infoState_723_);
v___x_725_ = lean_mk_thunk(v___f_724_);
v___f_726_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___lam__1___boxed), 2, 1);
lean_closure_set(v___f_726_, 0, v___x_725_);
lean_inc_n(v_stx_692_, 2);
v___x_727_ = l_Lean_Fmt_collectSyntaxLineInfos(v_stx_692_);
lean_inc_ref(v_fileMap_698_);
v___x_728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_728_, 0, v_env_697_);
lean_ctor_set(v___x_728_, 1, v_fileMap_698_);
lean_ctor_set(v___x_728_, 2, v___f_726_);
lean_ctor_set(v___x_728_, 3, v_opts_703_);
lean_ctor_set(v___x_728_, 4, v___x_727_);
v___x_729_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 1);
lean_closure_set(v___x_729_, 0, v_stx_692_);
v___x_730_ = l_Lean_FmtM_run___redArg(v___x_728_, v___x_729_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___y_733_; lean_object* v___x_745_; 
lean_dec_ref(v_opts_703_);
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_n(v_a_731_, 2);
lean_dec_ref_known(v___x_730_, 1);
v___x_745_ = l_Lean_Fmt_Error_ref_x3f(v_a_731_);
if (lean_obj_tag(v___x_745_) == 0)
{
v___y_733_ = v_stx_692_;
goto v___jp_732_;
}
else
{
lean_object* v_val_746_; 
lean_dec(v_stx_692_);
v_val_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v___x_745_, 1);
v___y_733_ = v_val_746_;
goto v___jp_732_;
}
v___jp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = l_Lean_Linter_linter_fmt_missing;
v___x_735_ = lean_obj_once(&l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1, &l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1_once, _init_l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__1);
switch(lean_obj_tag(v_a_731_))
{
case 0:
{
lean_object* v___x_736_; 
lean_dec_ref_known(v_a_731_, 0);
v___x_736_ = ((lean_object*)(l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___closed__2));
v___y_706_ = v___y_733_;
v___y_707_ = v___x_735_;
v___y_708_ = v___x_734_;
v___y_709_ = v___x_736_;
goto v___jp_705_;
}
case 1:
{
lean_object* v_err_737_; 
v_err_737_ = lean_ctor_get(v_a_731_, 0);
lean_inc_ref(v_err_737_);
lean_dec_ref_known(v_a_731_, 1);
if (lean_obj_tag(v_err_737_) == 0)
{
lean_object* v_msg_738_; 
v_msg_738_ = lean_ctor_get(v_err_737_, 0);
lean_inc_ref(v_msg_738_);
lean_dec_ref_known(v_err_737_, 1);
v___y_706_ = v___y_733_;
v___y_707_ = v___x_735_;
v___y_708_ = v___x_734_;
v___y_709_ = v_msg_738_;
goto v___jp_705_;
}
else
{
lean_object* v_msg_739_; 
v_msg_739_ = lean_ctor_get(v_err_737_, 1);
lean_inc_ref(v_msg_739_);
lean_dec_ref(v_err_737_);
v___y_706_ = v___y_733_;
v___y_707_ = v___x_735_;
v___y_708_ = v___x_734_;
v___y_709_ = v_msg_739_;
goto v___jp_705_;
}
}
case 2:
{
lean_object* v_err_740_; 
v_err_740_ = lean_ctor_get(v_a_731_, 0);
lean_inc_ref(v_err_740_);
lean_dec_ref_known(v_a_731_, 1);
if (lean_obj_tag(v_err_740_) == 0)
{
lean_object* v_msg_741_; 
v_msg_741_ = lean_ctor_get(v_err_740_, 2);
lean_inc_ref(v_msg_741_);
lean_dec_ref_known(v_err_740_, 3);
v___y_706_ = v___y_733_;
v___y_707_ = v___x_735_;
v___y_708_ = v___x_734_;
v___y_709_ = v_msg_741_;
goto v___jp_705_;
}
else
{
lean_object* v_msg_742_; 
v_msg_742_ = lean_ctor_get(v_err_740_, 1);
lean_inc_ref(v_msg_742_);
lean_dec_ref_known(v_err_740_, 2);
v___y_706_ = v___y_733_;
v___y_707_ = v___x_735_;
v___y_708_ = v___x_734_;
v___y_709_ = v_msg_742_;
goto v___jp_705_;
}
}
default: 
{
lean_object* v_err_743_; lean_object* v_msg_744_; 
v_err_743_ = lean_ctor_get(v_a_731_, 0);
lean_inc_ref(v_err_743_);
lean_dec_ref_known(v_a_731_, 1);
v_msg_744_ = lean_ctor_get(v_err_743_, 1);
lean_inc_ref(v_msg_744_);
lean_dec_ref(v_err_743_);
v___y_706_ = v___y_733_;
v___y_707_ = v___x_735_;
v___y_708_ = v___x_734_;
v___y_709_ = v_msg_744_;
goto v___jp_705_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v_toState_748_; lean_object* v_missingFormatters_749_; lean_object* v_partialFormatters_750_; lean_object* v_buckets_751_; lean_object* v___x_752_; size_t v_sz_753_; size_t v___x_754_; lean_object* v___x_755_; 
lean_dec(v_stx_692_);
v_a_747_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_730_, 1);
v_toState_748_ = lean_ctor_get(v_a_747_, 0);
lean_inc_ref(v_toState_748_);
lean_dec(v_a_747_);
v_missingFormatters_749_ = lean_ctor_get(v_toState_748_, 3);
lean_inc_ref(v_missingFormatters_749_);
v_partialFormatters_750_ = lean_ctor_get(v_toState_748_, 4);
lean_inc_ref(v_partialFormatters_750_);
lean_dec_ref(v_toState_748_);
v_buckets_751_ = lean_ctor_get(v_missingFormatters_749_, 1);
lean_inc_ref(v_buckets_751_);
lean_dec_ref(v_missingFormatters_749_);
v___x_752_ = lean_box(0);
v_sz_753_ = lean_array_size(v_buckets_751_);
v___x_754_ = ((size_t)0ULL);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__4(v_opts_703_, v_buckets_751_, v_sz_753_, v___x_754_, v___x_752_, v_a_693_, v_a_694_);
lean_dec_ref(v_buckets_751_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_buckets_756_; size_t v_sz_757_; lean_object* v___x_758_; 
lean_dec_ref_known(v___x_755_, 1);
v_buckets_756_ = lean_ctor_get(v_partialFormatters_750_, 1);
lean_inc_ref(v_buckets_756_);
lean_dec_ref(v_partialFormatters_750_);
v_sz_757_ = lean_array_size(v_buckets_756_);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__5(v_opts_703_, v_buckets_756_, v_sz_757_, v___x_754_, v___x_752_, v_a_693_, v_a_694_);
lean_dec_ref(v_buckets_756_);
lean_dec_ref(v_opts_703_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_758_, 0);
lean_dec(v_unused_766_);
v___x_760_ = v___x_758_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_dec(v___x_758_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 0, v___x_752_);
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_752_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
return v___x_758_;
}
}
else
{
lean_dec_ref(v_partialFormatters_750_);
lean_dec_ref(v_opts_703_);
return v___x_755_;
}
}
v___jp_705_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_710_, 0, v___y_709_);
v___x_711_ = l_Lean_MessageData_ofFormat(v___x_710_);
lean_inc_ref(v___y_707_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___y_707_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
lean_inc_ref(v___y_708_);
v___x_713_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1(v___y_708_, v___y_706_, v___x_712_, v_a_693_, v_a_694_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_721_; 
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v___x_713_, 0);
lean_dec(v_unused_722_);
v___x_715_ = v___x_713_;
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
else
{
lean_dec(v___x_713_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_box(0);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter___boxed(lean_object* v_stx_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(v_stx_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10(lean_object* v_msgData_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___redArg(v_msgData_772_, v___y_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10___boxed(lean_object* v_msgData_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter_spec__1_spec__3_spec__5_spec__10(v_msgData_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(lean_object* v_o_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v_env_787_; lean_object* v___x_788_; lean_object* v_toEnvExtension_789_; lean_object* v_asyncMode_790_; lean_object* v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v_merged_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v___x_785_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_786_ = lean_st_ref_get(v___y_783_);
v_env_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc_ref(v_env_787_);
lean_dec(v___x_786_);
v___x_788_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_789_ = lean_ctor_get(v___x_788_, 0);
v_asyncMode_790_ = lean_ctor_get(v_toEnvExtension_789_, 2);
v___x_791_ = lean_box(0);
v___x_792_ = 0;
v___x_793_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_785_, v___x_788_, v_env_787_, v_asyncMode_790_, v___x_791_, v___x_792_);
v_merged_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_793_, 1);
lean_dec(v_unused_803_);
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_merged_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v_merged_794_);
lean_ctor_set(v___x_796_, 0, v_o_782_);
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_o_782_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_merged_794_);
v___x_799_ = v_reuseFailAlloc_801_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg___boxed(lean_object* v_o_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_o_804_, v___y_805_);
lean_dec(v___y_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_scopes_813_; lean_object* v___x_814_; lean_object* v_opts_815_; lean_object* v___x_816_; 
v___x_811_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_812_ = lean_st_ref_get(v___y_809_);
v_scopes_813_ = lean_ctor_get(v___x_812_, 2);
lean_inc(v_scopes_813_);
lean_dec(v___x_812_);
v___x_814_ = l_List_head_x21___redArg(v___x_811_, v_scopes_813_);
lean_dec(v_scopes_813_);
v_opts_815_ = lean_ctor_get(v___x_814_, 1);
lean_inc_ref(v_opts_815_);
lean_dec(v___x_814_);
v___x_816_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_opts_815_, v___y_809_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0___boxed(lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0(lean_object* v_cmdStx_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_843_; 
v___x_825_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0(v___y_822_, v___y_823_);
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_843_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_843_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_843_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_toOptions_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_toOptions_830_ = lean_ctor_get(v_a_826_, 0);
lean_inc_ref(v_toOptions_830_);
lean_dec(v_a_826_);
v___x_831_ = l_Lean_Linter_linter_fmt_missing;
v___x_832_ = l_Lean_Option_get___at___00__private_Lean_Linter_Fmt_0__Lean_Linter_isIgnoredKind_spec__0(v_toOptions_830_, v___x_831_);
lean_dec_ref(v_toOptions_830_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_dec(v_cmdStx_821_);
v___x_833_ = lean_box(0);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_833_);
v___x_835_ = v___x_828_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
uint8_t v___x_837_; 
v___x_837_ = l_Lean_Syntax_hasMissing(v_cmdStx_821_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_del_object(v___x_828_);
v___x_838_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_checkMissingFormatter(v_cmdStx_821_, v___y_822_, v___y_823_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_841_; 
lean_dec(v_cmdStx_821_);
v___x_839_ = lean_box(0);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_839_);
v___x_841_ = v___x_828_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_fmtMissing___lam__0___boxed(lean_object* v_cmdStx_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Linter_fmtMissing___lam__0(v_cmdStx_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0(lean_object* v_o_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___redArg(v_o_859_, v___y_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0___boxed(lean_object* v_o_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_fmtMissing_spec__0_spec__0(v_o_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_Linter_fmtMissing));
v___x_871_ = l_Lean_Elab_Command_addLinter(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2____boxed(lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Linter_Fmt_0__Lean_Linter_initFn_00___x40_Lean_Linter_Fmt_830761699____hygCtx___hyg_2_();
return v_res_873_;
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
