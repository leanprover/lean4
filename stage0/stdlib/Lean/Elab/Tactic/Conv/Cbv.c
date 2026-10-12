// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Cbv
// Imports: public import Lean.Meta.Tactic.Cbv public import Lean.Elab.Tactic.Conv.Basic
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_updateLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_Cbv_cbv_warning;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "The `cbv` usage warning option is enabled. Disable it by setting `set_option cbv.warning false`."};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(57, 158, 11, 110, 229, 69, 84, 167)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalCbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(129, 239, 200, 20, 63, 246, 37, 189)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___boxed(lean_object*);
uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1_ = stack[0].m_obj;
lean_object* v_opt_2_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v_opts_1_, v_opt_2_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0___boxed(lean_object* v_opts_12_, lean_object* v_opt_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v_opts_12_, v_opt_13_);
lean_dec_ref(v_opt_13_);
lean_dec_ref(v_opts_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_){
_start:
{
lean_object* v___x_22_; lean_object* v_env_23_; uint8_t v___x_24_; lean_object* v_env_25_; lean_object* v___x_26_; lean_object* v_toCold_27_; lean_object* v_mctx_28_; lean_object* v_lctx_29_; lean_object* v_options_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_22_ = lean_st_ref_get(v___y_20_);
v_env_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc_ref(v_env_23_);
lean_dec(v___x_22_);
v___x_24_ = 0;
v_env_25_ = l_Lean_Environment_setRecordingDeps(v_env_23_, v___x_24_);
v___x_26_ = lean_st_ref_get(v___y_18_);
v_toCold_27_ = lean_ctor_get(v___y_19_, 0);
v_mctx_28_ = lean_ctor_get(v___x_26_, 0);
lean_inc_ref(v_mctx_28_);
lean_dec(v___x_26_);
v_lctx_29_ = lean_ctor_get(v___y_17_, 2);
v_options_30_ = lean_ctor_get(v_toCold_27_, 2);
lean_inc_ref(v_options_30_);
lean_inc_ref(v_lctx_29_);
v___x_31_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_31_, 0, v_env_25_);
lean_ctor_set(v___x_31_, 1, v_mctx_28_);
lean_ctor_set(v___x_31_, 2, v_lctx_29_);
lean_ctor_set(v___x_31_, 3, v_options_30_);
v___x_32_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v_msgData_16_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_16_ = stack[0].m_obj;
lean_object* v___y_17_ = stack[1].m_obj;
lean_object* v___y_18_ = stack[2].m_obj;
lean_object* v___y_19_ = stack[3].m_obj;
lean_object* v___y_20_ = stack[4].m_obj;
lean_object* v_res_34_;
v_res_34_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v_msgData_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_41_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_50_, uint8_t v___y_51_, lean_object* v_x_52_){
_start:
{
if (lean_obj_tag(v_x_52_) == 1)
{
lean_object* v_pre_53_; 
v_pre_53_ = lean_ctor_get(v_x_52_, 0);
switch(lean_obj_tag(v_pre_53_))
{
case 1:
{
lean_object* v_pre_54_; 
v_pre_54_ = lean_ctor_get(v_pre_53_, 0);
switch(lean_obj_tag(v_pre_54_))
{
case 0:
{
lean_object* v_str_55_; lean_object* v_str_56_; lean_object* v___x_57_; uint8_t v___x_58_; 
v_str_55_ = lean_ctor_get(v_x_52_, 1);
v_str_56_ = lean_ctor_get(v_pre_53_, 1);
v___x_57_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0));
v___x_58_ = lean_string_dec_eq(v_str_56_, v___x_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1));
v___x_60_ = lean_string_dec_eq(v_str_56_, v___x_59_);
if (v___x_60_ == 0)
{
return v___x_60_;
}
else
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2));
v___x_62_ = lean_string_dec_eq(v_str_55_, v___x_61_);
if (v___x_62_ == 0)
{
return v___x_62_;
}
else
{
return v_suppressElabErrors_50_;
}
}
}
else
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3));
v___x_64_ = lean_string_dec_eq(v_str_55_, v___x_63_);
if (v___x_64_ == 0)
{
return v___x_64_;
}
else
{
return v_suppressElabErrors_50_;
}
}
}
case 1:
{
lean_object* v_pre_65_; 
v_pre_65_ = lean_ctor_get(v_pre_54_, 0);
if (lean_obj_tag(v_pre_65_) == 0)
{
lean_object* v_str_66_; lean_object* v_str_67_; lean_object* v_str_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_str_66_ = lean_ctor_get(v_x_52_, 1);
v_str_67_ = lean_ctor_get(v_pre_53_, 1);
v_str_68_ = lean_ctor_get(v_pre_54_, 1);
v___x_69_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4));
v___x_70_ = lean_string_dec_eq(v_str_68_, v___x_69_);
if (v___x_70_ == 0)
{
return v___x_70_;
}
else
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5));
v___x_72_ = lean_string_dec_eq(v_str_67_, v___x_71_);
if (v___x_72_ == 0)
{
return v___x_72_;
}
else
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6));
v___x_74_ = lean_string_dec_eq(v_str_66_, v___x_73_);
if (v___x_74_ == 0)
{
return v___x_74_;
}
else
{
return v_suppressElabErrors_50_;
}
}
}
}
else
{
return v___y_51_;
}
}
default: 
{
return v___y_51_;
}
}
}
case 0:
{
lean_object* v_str_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v_str_75_ = lean_ctor_get(v_x_52_, 1);
v___x_76_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7));
v___x_77_ = lean_string_dec_eq(v_str_75_, v___x_76_);
if (v___x_77_ == 0)
{
return v___x_77_;
}
else
{
return v_suppressElabErrors_50_;
}
}
default: 
{
return v___y_51_;
}
}
}
else
{
return v___y_51_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_50_ = stack[0].m_num;
uint8_t v___y_51_ = stack[1].m_num;
lean_object* v_x_52_ = stack[2].m_obj;
uint8_t v_res_78_;
v_res_78_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(v_suppressElabErrors_50_, v___y_51_, v_x_52_);
stack->m_num = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_79_, lean_object* v___y_80_, lean_object* v_x_81_){
_start:
{
uint8_t v_suppressElabErrors_boxed_82_; uint8_t v___y_5190__boxed_83_; uint8_t v_res_84_; lean_object* v_r_85_; 
v_suppressElabErrors_boxed_82_ = lean_unbox(v_suppressElabErrors_79_);
v___y_5190__boxed_83_ = lean_unbox(v___y_80_);
v_res_84_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_82_, v___y_5190__boxed_83_, v_x_81_);
lean_dec(v_x_81_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(lean_object* v_ref_87_, lean_object* v_msgData_88_, uint8_t v_severity_89_, uint8_t v_isSilent_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___y_97_; lean_object* v___y_98_; uint8_t v___y_99_; lean_object* v___y_100_; uint8_t v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v_toCold_104_; lean_object* v___y_105_; lean_object* v___y_134_; lean_object* v___y_135_; uint8_t v___y_136_; lean_object* v___y_137_; uint8_t v___y_138_; lean_object* v___y_139_; uint8_t v___y_140_; lean_object* v___y_141_; lean_object* v___y_161_; lean_object* v___y_162_; uint8_t v___y_163_; lean_object* v___y_164_; uint8_t v___y_165_; uint8_t v___y_166_; lean_object* v___y_167_; uint8_t v___y_171_; uint8_t v___y_172_; uint8_t v___y_173_; uint8_t v___x_184_; uint8_t v___y_186_; uint8_t v___y_187_; uint8_t v___y_188_; uint8_t v___y_190_; uint8_t v___x_198_; 
v___x_184_ = 2;
v___x_198_ = l_Lean_instBEqMessageSeverity_beq(v_severity_89_, v___x_184_);
if (v___x_198_ == 0)
{
v___y_190_ = v___x_198_;
goto v___jp_189_;
}
else
{
uint8_t v___x_199_; 
lean_inc_ref(v_msgData_88_);
v___x_199_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_88_);
v___y_190_ = v___x_199_;
goto v___jp_189_;
}
v___jp_96_:
{
lean_object* v_currNamespace_106_; lean_object* v_openDecls_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_env_112_; lean_object* v_nextMacroScope_113_; lean_object* v_ngen_114_; lean_object* v_auxDeclNGen_115_; lean_object* v_traceState_116_; lean_object* v_cache_117_; lean_object* v_recordedDeps_118_; lean_object* v_messages_119_; lean_object* v_infoState_120_; lean_object* v_snapshotTasks_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_132_; 
v_currNamespace_106_ = lean_ctor_get(v_toCold_104_, 4);
v_openDecls_107_ = lean_ctor_get(v_toCold_104_, 5);
lean_inc(v_openDecls_107_);
lean_inc(v_currNamespace_106_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_currNamespace_106_);
lean_ctor_set(v___x_108_, 1, v_openDecls_107_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___y_98_);
lean_inc_ref(v___y_97_);
lean_inc_ref(v___y_100_);
v___x_110_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_110_, 0, v___y_100_);
lean_ctor_set(v___x_110_, 1, v___y_103_);
lean_ctor_set(v___x_110_, 2, v___y_102_);
lean_ctor_set(v___x_110_, 3, v___y_97_);
lean_ctor_set(v___x_110_, 4, v___x_109_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*5, v___y_99_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*5 + 1, v___y_101_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*5 + 2, v_isSilent_90_);
v___x_111_ = lean_st_ref_take(v___y_105_);
v_env_112_ = lean_ctor_get(v___x_111_, 0);
v_nextMacroScope_113_ = lean_ctor_get(v___x_111_, 1);
v_ngen_114_ = lean_ctor_get(v___x_111_, 2);
v_auxDeclNGen_115_ = lean_ctor_get(v___x_111_, 3);
v_traceState_116_ = lean_ctor_get(v___x_111_, 4);
v_cache_117_ = lean_ctor_get(v___x_111_, 5);
v_recordedDeps_118_ = lean_ctor_get(v___x_111_, 6);
v_messages_119_ = lean_ctor_get(v___x_111_, 7);
v_infoState_120_ = lean_ctor_get(v___x_111_, 8);
v_snapshotTasks_121_ = lean_ctor_get(v___x_111_, 9);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_132_ == 0)
{
v___x_123_ = v___x_111_;
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_snapshotTasks_121_);
lean_inc(v_infoState_120_);
lean_inc(v_messages_119_);
lean_inc(v_recordedDeps_118_);
lean_inc(v_cache_117_);
lean_inc(v_traceState_116_);
lean_inc(v_auxDeclNGen_115_);
lean_inc(v_ngen_114_);
lean_inc(v_nextMacroScope_113_);
lean_inc(v_env_112_);
lean_dec(v___x_111_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_125_ = lean_box(0);
v___x_126_ = l_Lean_MessageLog_add(v___x_110_, v_messages_119_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 7, v___x_126_);
v___x_128_ = v___x_123_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_env_112_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_nextMacroScope_113_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_ngen_114_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_auxDeclNGen_115_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v_traceState_116_);
lean_ctor_set(v_reuseFailAlloc_131_, 5, v_cache_117_);
lean_ctor_set(v_reuseFailAlloc_131_, 6, v_recordedDeps_118_);
lean_ctor_set(v_reuseFailAlloc_131_, 7, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_131_, 8, v_infoState_120_);
lean_ctor_set(v_reuseFailAlloc_131_, 9, v_snapshotTasks_121_);
v___x_128_ = v_reuseFailAlloc_131_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_st_ref_put(v___y_105_, v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_125_);
return v___x_130_;
}
}
}
v___jp_133_:
{
lean_object* v_fileName_142_; lean_object* v_fileMap_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_159_; 
v_fileName_142_ = lean_ctor_get(v___y_139_, 0);
v_fileMap_143_ = lean_ctor_get(v___y_139_, 1);
v___x_144_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_88_);
v___x_145_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v___x_144_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_159_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_159_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_159_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
lean_inc_ref_n(v_fileMap_143_, 2);
v___x_150_ = l_Lean_FileMap_toPosition(v_fileMap_143_, v___y_137_);
lean_dec(v___y_137_);
v___x_151_ = l_Lean_FileMap_toPosition(v_fileMap_143_, v___y_141_);
lean_dec(v___y_141_);
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
v___x_153_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0));
if (v___y_140_ == 0)
{
lean_del_object(v___x_148_);
lean_dec_ref(v___y_134_);
v___y_97_ = v___x_153_;
v___y_98_ = v_a_146_;
v___y_99_ = v___y_136_;
v___y_100_ = v_fileName_142_;
v___y_101_ = v___y_138_;
v___y_102_ = v___x_152_;
v___y_103_ = v___x_150_;
v_toCold_104_ = v___y_135_;
v___y_105_ = v___y_94_;
goto v___jp_96_;
}
else
{
uint8_t v___x_154_; 
lean_inc(v_a_146_);
v___x_154_ = l_Lean_MessageData_hasTag(v___y_134_, v_a_146_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_157_; 
lean_dec_ref_known(v___x_152_, 1);
lean_dec_ref(v___x_150_);
lean_dec(v_a_146_);
v___x_155_ = lean_box(0);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_155_);
v___x_157_ = v___x_148_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
else
{
lean_del_object(v___x_148_);
v___y_97_ = v___x_153_;
v___y_98_ = v_a_146_;
v___y_99_ = v___y_136_;
v___y_100_ = v_fileName_142_;
v___y_101_ = v___y_138_;
v___y_102_ = v___x_152_;
v___y_103_ = v___x_150_;
v_toCold_104_ = v___y_135_;
v___y_105_ = v___y_94_;
goto v___jp_96_;
}
}
}
}
v___jp_160_:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Syntax_getTailPos_x3f(v___y_164_, v___y_165_);
lean_dec(v___y_164_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_inc(v___y_167_);
v___y_134_ = v___y_161_;
v___y_135_ = v___y_162_;
v___y_136_ = v___y_165_;
v___y_137_ = v___y_167_;
v___y_138_ = v___y_166_;
v___y_139_ = v___y_162_;
v___y_140_ = v___y_163_;
v___y_141_ = v___y_167_;
goto v___jp_133_;
}
else
{
lean_object* v_val_169_; 
v_val_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v___x_168_, 1);
v___y_134_ = v___y_161_;
v___y_135_ = v___y_162_;
v___y_136_ = v___y_165_;
v___y_137_ = v___y_167_;
v___y_138_ = v___y_166_;
v___y_139_ = v___y_162_;
v___y_140_ = v___y_163_;
v___y_141_ = v_val_169_;
goto v___jp_133_;
}
}
v___jp_170_:
{
lean_object* v_toCold_174_; lean_object* v_ref_175_; uint8_t v_suppressElabErrors_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v_ref_180_; lean_object* v___x_181_; 
v_toCold_174_ = lean_ctor_get(v___y_93_, 0);
v_ref_175_ = lean_ctor_get(v___y_93_, 2);
v_suppressElabErrors_176_ = lean_ctor_get_uint8(v___y_93_, sizeof(void*)*3 + 2);
v___x_177_ = lean_box(v_suppressElabErrors_176_);
v___x_178_ = lean_box(v___y_171_);
v___f_179_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_179_, 0, v___x_177_);
lean_closure_set(v___f_179_, 1, v___x_178_);
v_ref_180_ = l_Lean_replaceRef(v_ref_87_, v_ref_175_);
v___x_181_ = l_Lean_Syntax_getPos_x3f(v_ref_180_, v___y_172_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___y_161_ = v___f_179_;
v___y_162_ = v_toCold_174_;
v___y_163_ = v_suppressElabErrors_176_;
v___y_164_ = v_ref_180_;
v___y_165_ = v___y_172_;
v___y_166_ = v___y_173_;
v___y_167_ = v___x_182_;
goto v___jp_160_;
}
else
{
lean_object* v_val_183_; 
v_val_183_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_val_183_);
lean_dec_ref_known(v___x_181_, 1);
v___y_161_ = v___f_179_;
v___y_162_ = v_toCold_174_;
v___y_163_ = v_suppressElabErrors_176_;
v___y_164_ = v_ref_180_;
v___y_165_ = v___y_172_;
v___y_166_ = v___y_173_;
v___y_167_ = v_val_183_;
goto v___jp_160_;
}
}
v___jp_185_:
{
if (v___y_188_ == 0)
{
v___y_171_ = v___y_186_;
v___y_172_ = v___y_187_;
v___y_173_ = v_severity_89_;
goto v___jp_170_;
}
else
{
v___y_171_ = v___y_186_;
v___y_172_ = v___y_187_;
v___y_173_ = v___x_184_;
goto v___jp_170_;
}
}
v___jp_189_:
{
if (v___y_190_ == 0)
{
uint8_t v___x_191_; uint8_t v___x_192_; 
v___x_191_ = 1;
v___x_192_ = l_Lean_instBEqMessageSeverity_beq(v_severity_89_, v___x_191_);
if (v___x_192_ == 0)
{
v___y_186_ = v___y_190_;
v___y_187_ = v___y_190_;
v___y_188_ = v___x_192_;
goto v___jp_185_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_193_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_93_);
v___x_194_ = l_Lean_warningAsError;
v___x_195_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v___x_193_, v___x_194_);
lean_dec_ref(v___x_193_);
v___y_186_ = v___y_190_;
v___y_187_ = v___y_190_;
v___y_188_ = v___x_195_;
goto v___jp_185_;
}
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; 
lean_dec_ref(v_msgData_88_);
v___x_196_ = lean_box(0);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_87_ = stack[0].m_obj;
lean_object* v_msgData_88_ = stack[1].m_obj;
uint8_t v_severity_89_ = stack[2].m_num;
uint8_t v_isSilent_90_ = stack[3].m_num;
lean_object* v___y_91_ = stack[4].m_obj;
lean_object* v___y_92_ = stack[5].m_obj;
lean_object* v___y_93_ = stack[6].m_obj;
lean_object* v___y_94_ = stack[7].m_obj;
lean_object* v_res_200_;
v_res_200_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_87_, v_msgData_88_, v_severity_89_, v_isSilent_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___boxed(lean_object* v_ref_201_, lean_object* v_msgData_202_, lean_object* v_severity_203_, lean_object* v_isSilent_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
uint8_t v_severity_boxed_210_; uint8_t v_isSilent_boxed_211_; lean_object* v_res_212_; 
v_severity_boxed_210_ = lean_unbox(v_severity_203_);
v_isSilent_boxed_211_ = lean_unbox(v_isSilent_204_);
v_res_212_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_201_, v_msgData_202_, v_severity_boxed_210_, v_isSilent_boxed_211_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v_ref_201_);
return v_res_212_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(lean_object* v_ref_213_, lean_object* v_msgData_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; 
v___x_224_ = 1;
v___x_225_ = 0;
v___x_226_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_213_, v_msgData_214_, v___x_224_, v___x_225_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
return v___x_226_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_213_ = stack[0].m_obj;
lean_object* v_msgData_214_ = stack[1].m_obj;
lean_object* v___y_215_ = stack[2].m_obj;
lean_object* v___y_216_ = stack[3].m_obj;
lean_object* v___y_217_ = stack[4].m_obj;
lean_object* v___y_218_ = stack[5].m_obj;
lean_object* v___y_219_ = stack[6].m_obj;
lean_object* v___y_220_ = stack[7].m_obj;
lean_object* v___y_221_ = stack[8].m_obj;
lean_object* v___y_222_ = stack[9].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(v_ref_213_, v_msgData_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1___boxed(lean_object* v_ref_228_, lean_object* v_msgData_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(v_ref_228_, v_msgData_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v_ref_228_);
return v_res_239_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1));
v___x_244_ = l_Lean_MessageData_ofFormat(v___x_243_);
return v___x_244_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(lean_object* v_stx_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_287_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_252_);
v___x_288_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_289_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v___x_287_, v___x_288_);
lean_dec_ref(v___x_287_);
if (v___x_289_ == 0)
{
goto v___jp_255_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2);
v___x_291_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(v_stx_245_, v___x_290_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_dec_ref_known(v___x_291_, 1);
goto v___jp_255_;
}
else
{
return v___x_291_;
}
}
v___jp_255_:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_247_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_258_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_a_257_);
lean_dec_ref_known(v___x_256_, 1);
v___x_258_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_a_257_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_270_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_270_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_270_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_270_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
if (lean_obj_tag(v_a_259_) == 0)
{
lean_object* v___x_263_; lean_object* v___x_265_; 
lean_dec_ref_known(v_a_259_, 0);
v___x_263_ = lean_box(0);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_263_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
else
{
lean_object* v_e_x27_267_; lean_object* v_proof_268_; lean_object* v___x_269_; 
lean_del_object(v___x_261_);
v_e_x27_267_ = lean_ctor_get(v_a_259_, 0);
lean_inc_ref(v_e_x27_267_);
v_proof_268_ = lean_ctor_get(v_a_259_, 1);
lean_inc_ref(v_proof_268_);
lean_dec_ref_known(v_a_259_, 2);
v___x_269_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_e_x27_267_, v_proof_268_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
return v___x_269_;
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_a_271_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_258_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_258_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_256_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_256_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalCbv___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_245_ = stack[0].m_obj;
lean_object* v___y_246_ = stack[1].m_obj;
lean_object* v___y_247_ = stack[2].m_obj;
lean_object* v___y_248_ = stack[3].m_obj;
lean_object* v___y_249_ = stack[4].m_obj;
lean_object* v___y_250_ = stack[5].m_obj;
lean_object* v___y_251_ = stack[6].m_obj;
lean_object* v___y_252_ = stack[7].m_obj;
lean_object* v___y_253_ = stack[8].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(v_stx_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed(lean_object* v_stx_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(v_stx_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v_stx_293_);
return v_res_303_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalCbv(lean_object* v_stx_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___f_314_; lean_object* v___x_315_; 
v___f_314_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed), 10, 1);
lean_closure_set(v___f_314_, 0, v_stx_304_);
v___x_315_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_314_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
return v___x_315_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalCbv_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_304_ = stack[0].m_obj;
lean_object* v_a_305_ = stack[1].m_obj;
lean_object* v_a_306_ = stack[2].m_obj;
lean_object* v_a_307_ = stack[3].m_obj;
lean_object* v_a_308_ = stack[4].m_obj;
lean_object* v_a_309_ = stack[5].m_obj;
lean_object* v_a_310_ = stack[6].m_obj;
lean_object* v_a_311_ = stack[7].m_obj;
lean_object* v_a_312_ = stack[8].m_obj;
lean_object* v_res_316_;
v_res_316_ = l_Lean_Elab_Tactic_Conv_evalCbv(v_stx_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___boxed(lean_object* v_stx_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Elab_Tactic_Conv_evalCbv(v_stx_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_327_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(lean_object* v_ref_328_, lean_object* v_msgData_329_, uint8_t v_severity_330_, uint8_t v_isSilent_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_328_, v_msgData_329_, v_severity_330_, v_isSilent_331_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
return v___x_341_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_328_ = stack[0].m_obj;
lean_object* v_msgData_329_ = stack[1].m_obj;
uint8_t v_severity_330_ = stack[2].m_num;
uint8_t v_isSilent_331_ = stack[3].m_num;
lean_object* v___y_332_ = stack[4].m_obj;
lean_object* v___y_333_ = stack[5].m_obj;
lean_object* v___y_334_ = stack[6].m_obj;
lean_object* v___y_335_ = stack[7].m_obj;
lean_object* v___y_336_ = stack[8].m_obj;
lean_object* v___y_337_ = stack[9].m_obj;
lean_object* v___y_338_ = stack[10].m_obj;
lean_object* v___y_339_ = stack[11].m_obj;
lean_object* v_res_342_;
v_res_342_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(v_ref_328_, v_msgData_329_, v_severity_330_, v_isSilent_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
stack->m_obj
 = v_res_342_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___boxed(lean_object* v_ref_343_, lean_object* v_msgData_344_, lean_object* v_severity_345_, lean_object* v_isSilent_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
uint8_t v_severity_boxed_356_; uint8_t v_isSilent_boxed_357_; lean_object* v_res_358_; 
v_severity_boxed_356_ = lean_unbox(v_severity_345_);
v_isSilent_boxed_357_ = lean_unbox(v_isSilent_346_);
v_res_358_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(v_ref_343_, v_msgData_344_, v_severity_boxed_356_, v_isSilent_boxed_357_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v_ref_343_);
return v_res_358_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1(){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_377_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_378_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4));
v___x_379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6));
v___x_380_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCbv___boxed), 10, 0);
v___x_381_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_377_, v___x_378_, v___x_379_, v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_382_;
v_res_382_ = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1();
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___boxed(lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1();
return v_res_384_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Cbv(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Cbv(builtin);
}
#ifdef __cplusplus
}
#endif
