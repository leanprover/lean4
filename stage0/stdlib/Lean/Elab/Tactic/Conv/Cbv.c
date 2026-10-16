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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(lean_object* v_msgData_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; lean_object* v_env_22_; uint8_t v___x_23_; lean_object* v_env_24_; lean_object* v___x_25_; lean_object* v_toCold_26_; lean_object* v_mctx_27_; lean_object* v_lctx_28_; lean_object* v_options_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_21_ = lean_st_ref_get(v___y_19_);
v_env_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_env_22_);
lean_dec(v___x_21_);
v___x_23_ = 0;
v_env_24_ = l_Lean_Environment_setRecordingDeps(v_env_22_, v___x_23_);
v___x_25_ = lean_st_ref_get(v___y_17_);
v_toCold_26_ = lean_ctor_get(v___y_18_, 0);
v_mctx_27_ = lean_ctor_get(v___x_25_, 0);
lean_inc_ref(v_mctx_27_);
lean_dec(v___x_25_);
v_lctx_28_ = lean_ctor_get(v___y_16_, 2);
v_options_29_ = lean_ctor_get(v_toCold_26_, 2);
lean_inc_ref(v_options_29_);
lean_inc_ref(v_lctx_28_);
v___x_30_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_30_, 0, v_env_24_);
lean_ctor_set(v___x_30_, 1, v_mctx_27_);
lean_ctor_set(v___x_30_, 2, v_lctx_28_);
lean_ctor_set(v___x_30_, 3, v_options_29_);
v___x_31_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v_msgData_15_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v_msgData_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
return v_res_39_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(uint8_t v_suppressElabErrors_48_, lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 1)
{
lean_object* v_pre_50_; 
v_pre_50_ = lean_ctor_get(v_x_49_, 0);
switch(lean_obj_tag(v_pre_50_))
{
case 1:
{
lean_object* v_pre_51_; 
v_pre_51_ = lean_ctor_get(v_pre_50_, 0);
switch(lean_obj_tag(v_pre_51_))
{
case 0:
{
lean_object* v_str_52_; lean_object* v_str_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v_str_52_ = lean_ctor_get(v_x_49_, 1);
v_str_53_ = lean_ctor_get(v_pre_50_, 1);
v___x_54_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0));
v___x_55_ = lean_string_dec_eq(v_str_53_, v___x_54_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1));
v___x_57_ = lean_string_dec_eq(v_str_53_, v___x_56_);
if (v___x_57_ == 0)
{
return v___x_57_;
}
else
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2));
v___x_59_ = lean_string_dec_eq(v_str_52_, v___x_58_);
if (v___x_59_ == 0)
{
return v___x_59_;
}
else
{
return v_suppressElabErrors_48_;
}
}
}
else
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3));
v___x_61_ = lean_string_dec_eq(v_str_52_, v___x_60_);
if (v___x_61_ == 0)
{
return v___x_61_;
}
else
{
return v_suppressElabErrors_48_;
}
}
}
case 1:
{
lean_object* v_pre_62_; 
v_pre_62_ = lean_ctor_get(v_pre_51_, 0);
if (lean_obj_tag(v_pre_62_) == 0)
{
lean_object* v_str_63_; lean_object* v_str_64_; lean_object* v_str_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_str_63_ = lean_ctor_get(v_x_49_, 1);
v_str_64_ = lean_ctor_get(v_pre_50_, 1);
v_str_65_ = lean_ctor_get(v_pre_51_, 1);
v___x_66_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4));
v___x_67_ = lean_string_dec_eq(v_str_65_, v___x_66_);
if (v___x_67_ == 0)
{
return v___x_67_;
}
else
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5));
v___x_69_ = lean_string_dec_eq(v_str_64_, v___x_68_);
if (v___x_69_ == 0)
{
return v___x_69_;
}
else
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6));
v___x_71_ = lean_string_dec_eq(v_str_63_, v___x_70_);
if (v___x_71_ == 0)
{
return v___x_71_;
}
else
{
return v_suppressElabErrors_48_;
}
}
}
}
else
{
uint8_t v___x_72_; 
v___x_72_ = 0;
return v___x_72_;
}
}
default: 
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
}
}
case 0:
{
lean_object* v_str_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_str_74_ = lean_ctor_get(v_x_49_, 1);
v___x_75_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7));
v___x_76_ = lean_string_dec_eq(v_str_74_, v___x_75_);
if (v___x_76_ == 0)
{
return v___x_76_;
}
else
{
return v_suppressElabErrors_48_;
}
}
default: 
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
}
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_79_, lean_object* v_x_80_){
_start:
{
uint8_t v_suppressElabErrors_boxed_81_; uint8_t v_res_82_; lean_object* v_r_83_; 
v_suppressElabErrors_boxed_81_ = lean_unbox(v_suppressElabErrors_79_);
v_res_82_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(v_suppressElabErrors_boxed_81_, v_x_80_);
lean_dec(v_x_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(lean_object* v_ref_85_, lean_object* v_msgData_86_, uint8_t v_severity_87_, uint8_t v_isSilent_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
uint8_t v___y_95_; lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v___y_98_; uint8_t v___y_99_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v_toCold_102_; lean_object* v___y_103_; lean_object* v___y_132_; lean_object* v___y_133_; uint8_t v___y_134_; lean_object* v___y_135_; uint8_t v___y_136_; uint8_t v___y_137_; lean_object* v___y_138_; lean_object* v___y_139_; lean_object* v___y_159_; lean_object* v___y_160_; uint8_t v___y_161_; uint8_t v___y_162_; uint8_t v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; uint8_t v___y_169_; uint8_t v___y_170_; uint8_t v___x_180_; uint8_t v___y_182_; uint8_t v___x_188_; 
v___x_180_ = 2;
v___x_188_ = l_Lean_instBEqMessageSeverity_beq(v_severity_87_, v___x_180_);
if (v___x_188_ == 0)
{
v___y_182_ = v___x_188_;
goto v___jp_181_;
}
else
{
uint8_t v___x_189_; 
lean_inc_ref(v_msgData_86_);
v___x_189_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_86_);
if (v___x_189_ == 0)
{
v___y_182_ = v___x_189_;
goto v___jp_181_;
}
else
{
lean_object* v___x_190_; lean_object* v___x_191_; 
lean_dec_ref(v_msgData_86_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
v___jp_94_:
{
lean_object* v_currNamespace_104_; lean_object* v_openDecls_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_env_110_; lean_object* v_nextMacroScope_111_; lean_object* v_ngen_112_; lean_object* v_auxDeclNGen_113_; lean_object* v_traceState_114_; lean_object* v_cache_115_; lean_object* v_recordedDeps_116_; lean_object* v_messages_117_; lean_object* v_infoState_118_; lean_object* v_snapshotTasks_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_130_; 
v_currNamespace_104_ = lean_ctor_get(v_toCold_102_, 4);
v_openDecls_105_ = lean_ctor_get(v_toCold_102_, 5);
lean_inc(v_openDecls_105_);
lean_inc(v_currNamespace_104_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_currNamespace_104_);
lean_ctor_set(v___x_106_, 1, v_openDecls_105_);
v___x_107_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___y_98_);
lean_inc_ref(v___y_101_);
lean_inc_ref(v___y_100_);
v___x_108_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_108_, 0, v___y_100_);
lean_ctor_set(v___x_108_, 1, v___y_97_);
lean_ctor_set(v___x_108_, 2, v___y_96_);
lean_ctor_set(v___x_108_, 3, v___y_101_);
lean_ctor_set(v___x_108_, 4, v___x_107_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*5, v___y_99_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*5 + 1, v___y_95_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*5 + 2, v_isSilent_88_);
v___x_109_ = lean_st_ref_take(v___y_103_);
v_env_110_ = lean_ctor_get(v___x_109_, 0);
v_nextMacroScope_111_ = lean_ctor_get(v___x_109_, 1);
v_ngen_112_ = lean_ctor_get(v___x_109_, 2);
v_auxDeclNGen_113_ = lean_ctor_get(v___x_109_, 3);
v_traceState_114_ = lean_ctor_get(v___x_109_, 4);
v_cache_115_ = lean_ctor_get(v___x_109_, 5);
v_recordedDeps_116_ = lean_ctor_get(v___x_109_, 6);
v_messages_117_ = lean_ctor_get(v___x_109_, 7);
v_infoState_118_ = lean_ctor_get(v___x_109_, 8);
v_snapshotTasks_119_ = lean_ctor_get(v___x_109_, 9);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_130_ == 0)
{
v___x_121_ = v___x_109_;
v_isShared_122_ = v_isSharedCheck_130_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_snapshotTasks_119_);
lean_inc(v_infoState_118_);
lean_inc(v_messages_117_);
lean_inc(v_recordedDeps_116_);
lean_inc(v_cache_115_);
lean_inc(v_traceState_114_);
lean_inc(v_auxDeclNGen_113_);
lean_inc(v_ngen_112_);
lean_inc(v_nextMacroScope_111_);
lean_inc(v_env_110_);
lean_dec(v___x_109_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_130_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_123_ = lean_box(0);
v___x_124_ = l_Lean_MessageLog_add(v___x_108_, v_messages_117_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 7, v___x_124_);
v___x_126_ = v___x_121_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_env_110_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_nextMacroScope_111_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v_ngen_112_);
lean_ctor_set(v_reuseFailAlloc_129_, 3, v_auxDeclNGen_113_);
lean_ctor_set(v_reuseFailAlloc_129_, 4, v_traceState_114_);
lean_ctor_set(v_reuseFailAlloc_129_, 5, v_cache_115_);
lean_ctor_set(v_reuseFailAlloc_129_, 6, v_recordedDeps_116_);
lean_ctor_set(v_reuseFailAlloc_129_, 7, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_129_, 8, v_infoState_118_);
lean_ctor_set(v_reuseFailAlloc_129_, 9, v_snapshotTasks_119_);
v___x_126_ = v_reuseFailAlloc_129_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_st_ref_put(v___y_103_, v___x_126_);
v___x_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_123_);
return v___x_128_;
}
}
}
v___jp_131_:
{
lean_object* v_fileName_140_; lean_object* v_fileMap_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_157_; 
v_fileName_140_ = lean_ctor_get(v___y_135_, 0);
v_fileMap_141_ = lean_ctor_get(v___y_135_, 1);
v___x_142_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_86_);
v___x_143_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v___x_142_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_157_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_157_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_157_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
lean_inc_ref_n(v_fileMap_141_, 2);
v___x_148_ = l_Lean_FileMap_toPosition(v_fileMap_141_, v___y_138_);
lean_dec(v___y_138_);
v___x_149_ = l_Lean_FileMap_toPosition(v_fileMap_141_, v___y_139_);
lean_dec(v___y_139_);
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
v___x_151_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0));
if (v___y_136_ == 0)
{
lean_del_object(v___x_146_);
lean_dec_ref(v___y_133_);
v___y_95_ = v___y_134_;
v___y_96_ = v___x_150_;
v___y_97_ = v___x_148_;
v___y_98_ = v_a_144_;
v___y_99_ = v___y_137_;
v___y_100_ = v_fileName_140_;
v___y_101_ = v___x_151_;
v_toCold_102_ = v___y_132_;
v___y_103_ = v___y_92_;
goto v___jp_94_;
}
else
{
uint8_t v___x_152_; 
lean_inc(v_a_144_);
v___x_152_ = l_Lean_MessageData_hasTag(v___y_133_, v_a_144_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_155_; 
lean_dec_ref_known(v___x_150_, 1);
lean_dec_ref(v___x_148_);
lean_dec(v_a_144_);
v___x_153_ = lean_box(0);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_153_);
v___x_155_ = v___x_146_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
else
{
lean_del_object(v___x_146_);
v___y_95_ = v___y_134_;
v___y_96_ = v___x_150_;
v___y_97_ = v___x_148_;
v___y_98_ = v_a_144_;
v___y_99_ = v___y_137_;
v___y_100_ = v_fileName_140_;
v___y_101_ = v___x_151_;
v_toCold_102_ = v___y_132_;
v___y_103_ = v___y_92_;
goto v___jp_94_;
}
}
}
}
v___jp_158_:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Syntax_getTailPos_x3f(v___y_164_, v___y_163_);
lean_dec(v___y_164_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_inc(v___y_165_);
v___y_132_ = v___y_159_;
v___y_133_ = v___y_160_;
v___y_134_ = v___y_162_;
v___y_135_ = v___y_159_;
v___y_136_ = v___y_161_;
v___y_137_ = v___y_163_;
v___y_138_ = v___y_165_;
v___y_139_ = v___y_165_;
goto v___jp_131_;
}
else
{
lean_object* v_val_167_; 
v_val_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_val_167_);
lean_dec_ref_known(v___x_166_, 1);
v___y_132_ = v___y_159_;
v___y_133_ = v___y_160_;
v___y_134_ = v___y_162_;
v___y_135_ = v___y_159_;
v___y_136_ = v___y_161_;
v___y_137_ = v___y_163_;
v___y_138_ = v___y_165_;
v___y_139_ = v_val_167_;
goto v___jp_131_;
}
}
v___jp_168_:
{
lean_object* v_toCold_171_; lean_object* v_ref_172_; uint8_t v_suppressElabErrors_173_; lean_object* v___x_174_; lean_object* v___f_175_; lean_object* v_ref_176_; lean_object* v___x_177_; 
v_toCold_171_ = lean_ctor_get(v___y_91_, 0);
v_ref_172_ = lean_ctor_get(v___y_91_, 2);
v_suppressElabErrors_173_ = lean_ctor_get_uint8(v___y_91_, sizeof(void*)*3 + 2);
v___x_174_ = lean_box(v_suppressElabErrors_173_);
v___f_175_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_175_, 0, v___x_174_);
v_ref_176_ = l_Lean_replaceRef(v_ref_85_, v_ref_172_);
v___x_177_ = l_Lean_Syntax_getPos_x3f(v_ref_176_, v___y_169_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___y_159_ = v_toCold_171_;
v___y_160_ = v___f_175_;
v___y_161_ = v_suppressElabErrors_173_;
v___y_162_ = v___y_170_;
v___y_163_ = v___y_169_;
v___y_164_ = v_ref_176_;
v___y_165_ = v___x_178_;
goto v___jp_158_;
}
else
{
lean_object* v_val_179_; 
v_val_179_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_val_179_);
lean_dec_ref_known(v___x_177_, 1);
v___y_159_ = v_toCold_171_;
v___y_160_ = v___f_175_;
v___y_161_ = v_suppressElabErrors_173_;
v___y_162_ = v___y_170_;
v___y_163_ = v___y_169_;
v___y_164_ = v_ref_176_;
v___y_165_ = v_val_179_;
goto v___jp_158_;
}
}
v___jp_181_:
{
uint8_t v___x_183_; uint8_t v___x_184_; 
v___x_183_ = 1;
v___x_184_ = l_Lean_instBEqMessageSeverity_beq(v_severity_87_, v___x_183_);
if (v___x_184_ == 0)
{
v___y_169_ = v___y_182_;
v___y_170_ = v_severity_87_;
goto v___jp_168_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_91_);
v___x_186_ = l_Lean_warningAsError;
v___x_187_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v___x_185_, v___x_186_);
lean_dec_ref(v___x_185_);
if (v___x_187_ == 0)
{
v___y_169_ = v___y_182_;
v___y_170_ = v_severity_87_;
goto v___jp_168_;
}
else
{
v___y_169_ = v___y_182_;
v___y_170_ = v___x_180_;
goto v___jp_168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___boxed(lean_object* v_ref_192_, lean_object* v_msgData_193_, lean_object* v_severity_194_, lean_object* v_isSilent_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
uint8_t v_severity_boxed_201_; uint8_t v_isSilent_boxed_202_; lean_object* v_res_203_; 
v_severity_boxed_201_ = lean_unbox(v_severity_194_);
v_isSilent_boxed_202_ = lean_unbox(v_isSilent_195_);
v_res_203_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_192_, v_msgData_193_, v_severity_boxed_201_, v_isSilent_boxed_202_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v_ref_192_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(lean_object* v_ref_204_, lean_object* v_msgData_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
uint8_t v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; 
v___x_215_ = 1;
v___x_216_ = 0;
v___x_217_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_204_, v_msgData_205_, v___x_215_, v___x_216_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1___boxed(lean_object* v_ref_218_, lean_object* v_msgData_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(v_ref_218_, v_msgData_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v_ref_218_);
return v_res_229_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1));
v___x_234_ = l_Lean_MessageData_ofFormat(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(lean_object* v_stx_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_277_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_242_);
v___x_278_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_279_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v___x_277_, v___x_278_);
lean_dec_ref(v___x_277_);
if (v___x_279_ == 0)
{
goto v___jp_245_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2);
v___x_281_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(v_stx_235_, v___x_280_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_dec_ref_known(v___x_281_, 1);
goto v___jp_245_;
}
else
{
return v___x_281_;
}
}
v___jp_245_:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_237_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_248_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 1);
v___x_248_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_a_247_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_260_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_260_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_260_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_260_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
if (lean_obj_tag(v_a_249_) == 0)
{
lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec_ref_known(v_a_249_, 0);
v___x_253_ = lean_box(0);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
else
{
lean_object* v_e_x27_257_; lean_object* v_proof_258_; lean_object* v___x_259_; 
lean_del_object(v___x_251_);
v_e_x27_257_ = lean_ctor_get(v_a_249_, 0);
lean_inc_ref(v_e_x27_257_);
v_proof_258_ = lean_ctor_get(v_a_249_, 1);
lean_inc_ref(v_proof_258_);
lean_dec_ref_known(v_a_249_, 2);
v___x_259_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_e_x27_257_, v_proof_258_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
return v___x_259_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_248_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_248_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_246_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_246_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed(lean_object* v_stx_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(v_stx_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v_stx_282_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv(lean_object* v_stx_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___f_303_; lean_object* v___x_304_; 
v___f_303_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed), 10, 1);
lean_closure_set(v___f_303_, 0, v_stx_293_);
v___x_304_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_303_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___boxed(lean_object* v_stx_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Elab_Tactic_Conv_evalCbv(v_stx_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(lean_object* v_ref_316_, lean_object* v_msgData_317_, uint8_t v_severity_318_, uint8_t v_isSilent_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_316_, v_msgData_317_, v_severity_318_, v_isSilent_319_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___boxed(lean_object* v_ref_330_, lean_object* v_msgData_331_, lean_object* v_severity_332_, lean_object* v_isSilent_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
uint8_t v_severity_boxed_343_; uint8_t v_isSilent_boxed_344_; lean_object* v_res_345_; 
v_severity_boxed_343_ = lean_unbox(v_severity_332_);
v_isSilent_boxed_344_ = lean_unbox(v_isSilent_333_);
v_res_345_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(v_ref_330_, v_msgData_331_, v_severity_boxed_343_, v_isSilent_boxed_344_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v_ref_330_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1(){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_364_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_365_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4));
v___x_366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6));
v___x_367_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCbv___boxed), 10, 0);
v___x_368_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_364_, v___x_365_, v___x_366_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___boxed(lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1();
return v_res_370_;
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
