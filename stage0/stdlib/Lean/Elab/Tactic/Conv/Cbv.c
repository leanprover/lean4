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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
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
lean_object* v___x_21_; lean_object* v_env_22_; lean_object* v___x_23_; lean_object* v_mctx_24_; lean_object* v_lctx_25_; lean_object* v_options_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_21_ = lean_st_ref_get(v___y_19_);
v_env_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_env_22_);
lean_dec(v___x_21_);
v___x_23_ = lean_st_ref_get(v___y_17_);
v_mctx_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc_ref(v_mctx_24_);
lean_dec(v___x_23_);
v_lctx_25_ = lean_ctor_get(v___y_16_, 2);
v_options_26_ = lean_ctor_get(v___y_18_, 2);
lean_inc_ref(v_options_26_);
lean_inc_ref(v_lctx_25_);
v___x_27_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_27_, 0, v_env_22_);
lean_ctor_set(v___x_27_, 1, v_mctx_24_);
lean_ctor_set(v___x_27_, 2, v_lctx_25_);
lean_ctor_set(v___x_27_, 3, v_options_26_);
v___x_28_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v_msgData_15_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v_msgData_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
return v_res_36_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(uint8_t v___y_45_, uint8_t v_suppressElabErrors_46_, lean_object* v_x_47_){
_start:
{
if (lean_obj_tag(v_x_47_) == 1)
{
lean_object* v_pre_48_; 
v_pre_48_ = lean_ctor_get(v_x_47_, 0);
switch(lean_obj_tag(v_pre_48_))
{
case 1:
{
lean_object* v_pre_49_; 
v_pre_49_ = lean_ctor_get(v_pre_48_, 0);
switch(lean_obj_tag(v_pre_49_))
{
case 0:
{
lean_object* v_str_50_; lean_object* v_str_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v_str_50_ = lean_ctor_get(v_x_47_, 1);
v_str_51_ = lean_ctor_get(v_pre_48_, 1);
v___x_52_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0));
v___x_53_ = lean_string_dec_eq(v_str_51_, v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1));
v___x_55_ = lean_string_dec_eq(v_str_51_, v___x_54_);
if (v___x_55_ == 0)
{
return v___y_45_;
}
else
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2));
v___x_57_ = lean_string_dec_eq(v_str_50_, v___x_56_);
if (v___x_57_ == 0)
{
return v___y_45_;
}
else
{
return v_suppressElabErrors_46_;
}
}
}
else
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3));
v___x_59_ = lean_string_dec_eq(v_str_50_, v___x_58_);
if (v___x_59_ == 0)
{
return v___y_45_;
}
else
{
return v_suppressElabErrors_46_;
}
}
}
case 1:
{
lean_object* v_pre_60_; 
v_pre_60_ = lean_ctor_get(v_pre_49_, 0);
if (lean_obj_tag(v_pre_60_) == 0)
{
lean_object* v_str_61_; lean_object* v_str_62_; lean_object* v_str_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_str_61_ = lean_ctor_get(v_x_47_, 1);
v_str_62_ = lean_ctor_get(v_pre_48_, 1);
v_str_63_ = lean_ctor_get(v_pre_49_, 1);
v___x_64_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4));
v___x_65_ = lean_string_dec_eq(v_str_63_, v___x_64_);
if (v___x_65_ == 0)
{
return v___y_45_;
}
else
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5));
v___x_67_ = lean_string_dec_eq(v_str_62_, v___x_66_);
if (v___x_67_ == 0)
{
return v___y_45_;
}
else
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6));
v___x_69_ = lean_string_dec_eq(v_str_61_, v___x_68_);
if (v___x_69_ == 0)
{
return v___y_45_;
}
else
{
return v_suppressElabErrors_46_;
}
}
}
}
else
{
return v___y_45_;
}
}
default: 
{
return v___y_45_;
}
}
}
case 0:
{
lean_object* v_str_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_str_70_ = lean_ctor_get(v_x_47_, 1);
v___x_71_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7));
v___x_72_ = lean_string_dec_eq(v_str_70_, v___x_71_);
if (v___x_72_ == 0)
{
return v___y_45_;
}
else
{
return v_suppressElabErrors_46_;
}
}
default: 
{
return v___y_45_;
}
}
}
else
{
return v___y_45_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_73_, lean_object* v_suppressElabErrors_74_, lean_object* v_x_75_){
_start:
{
uint8_t v___y_4796__boxed_76_; uint8_t v_suppressElabErrors_boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v___y_4796__boxed_76_ = lean_unbox(v___y_73_);
v_suppressElabErrors_boxed_77_ = lean_unbox(v_suppressElabErrors_74_);
v_res_78_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(v___y_4796__boxed_76_, v_suppressElabErrors_boxed_77_, v_x_75_);
lean_dec(v_x_75_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(lean_object* v_ref_81_, lean_object* v_msgData_82_, uint8_t v_severity_83_, uint8_t v_isSilent_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___y_91_; lean_object* v___y_92_; lean_object* v___y_93_; uint8_t v___y_94_; lean_object* v___y_95_; uint8_t v___y_96_; lean_object* v___y_97_; lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v___y_128_; lean_object* v___y_129_; uint8_t v___y_130_; lean_object* v___y_131_; uint8_t v___y_132_; uint8_t v___y_133_; lean_object* v___y_134_; lean_object* v___y_135_; lean_object* v___y_153_; lean_object* v___y_154_; uint8_t v___y_155_; lean_object* v___y_156_; lean_object* v___y_157_; uint8_t v___y_158_; uint8_t v___y_159_; lean_object* v___y_160_; lean_object* v___y_164_; lean_object* v___y_165_; uint8_t v___y_166_; uint8_t v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; uint8_t v___y_170_; uint8_t v___x_175_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_180_; uint8_t v___y_181_; uint8_t v___y_182_; uint8_t v___y_183_; uint8_t v___y_185_; uint8_t v___x_200_; 
v___x_175_ = 2;
v___x_200_ = l_Lean_instBEqMessageSeverity_beq(v_severity_83_, v___x_175_);
if (v___x_200_ == 0)
{
v___y_185_ = v___x_200_;
goto v___jp_184_;
}
else
{
uint8_t v___x_201_; 
lean_inc_ref(v_msgData_82_);
v___x_201_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_82_);
v___y_185_ = v___x_201_;
goto v___jp_184_;
}
v___jp_90_:
{
lean_object* v___x_100_; lean_object* v_currNamespace_101_; lean_object* v_openDecls_102_; lean_object* v_env_103_; lean_object* v_nextMacroScope_104_; lean_object* v_ngen_105_; lean_object* v_auxDeclNGen_106_; lean_object* v_traceState_107_; lean_object* v_cache_108_; lean_object* v_messages_109_; lean_object* v_infoState_110_; lean_object* v_snapshotTasks_111_; lean_object* v_newDecls_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_126_; 
v___x_100_ = lean_st_ref_take(v___y_99_);
v_currNamespace_101_ = lean_ctor_get(v___y_98_, 6);
v_openDecls_102_ = lean_ctor_get(v___y_98_, 7);
v_env_103_ = lean_ctor_get(v___x_100_, 0);
v_nextMacroScope_104_ = lean_ctor_get(v___x_100_, 1);
v_ngen_105_ = lean_ctor_get(v___x_100_, 2);
v_auxDeclNGen_106_ = lean_ctor_get(v___x_100_, 3);
v_traceState_107_ = lean_ctor_get(v___x_100_, 4);
v_cache_108_ = lean_ctor_get(v___x_100_, 5);
v_messages_109_ = lean_ctor_get(v___x_100_, 6);
v_infoState_110_ = lean_ctor_get(v___x_100_, 7);
v_snapshotTasks_111_ = lean_ctor_get(v___x_100_, 8);
v_newDecls_112_ = lean_ctor_get(v___x_100_, 9);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_126_ == 0)
{
v___x_114_ = v___x_100_;
v_isShared_115_ = v_isSharedCheck_126_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_newDecls_112_);
lean_inc(v_snapshotTasks_111_);
lean_inc(v_infoState_110_);
lean_inc(v_messages_109_);
lean_inc(v_cache_108_);
lean_inc(v_traceState_107_);
lean_inc(v_auxDeclNGen_106_);
lean_inc(v_ngen_105_);
lean_inc(v_nextMacroScope_104_);
lean_inc(v_env_103_);
lean_dec(v___x_100_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_126_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
lean_inc(v_openDecls_102_);
lean_inc(v_currNamespace_101_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v_currNamespace_101_);
lean_ctor_set(v___x_116_, 1, v_openDecls_102_);
v___x_117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___y_97_);
lean_inc_ref(v___y_95_);
lean_inc_ref(v___y_91_);
v___x_118_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_118_, 0, v___y_91_);
lean_ctor_set(v___x_118_, 1, v___y_93_);
lean_ctor_set(v___x_118_, 2, v___y_92_);
lean_ctor_set(v___x_118_, 3, v___y_95_);
lean_ctor_set(v___x_118_, 4, v___x_117_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*5, v___y_96_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*5 + 1, v___y_94_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*5 + 2, v_isSilent_84_);
v___x_119_ = l_Lean_MessageLog_add(v___x_118_, v_messages_109_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 6, v___x_119_);
v___x_121_ = v___x_114_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_env_103_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_nextMacroScope_104_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_ngen_105_);
lean_ctor_set(v_reuseFailAlloc_125_, 3, v_auxDeclNGen_106_);
lean_ctor_set(v_reuseFailAlloc_125_, 4, v_traceState_107_);
lean_ctor_set(v_reuseFailAlloc_125_, 5, v_cache_108_);
lean_ctor_set(v_reuseFailAlloc_125_, 6, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_125_, 7, v_infoState_110_);
lean_ctor_set(v_reuseFailAlloc_125_, 8, v_snapshotTasks_111_);
lean_ctor_set(v_reuseFailAlloc_125_, 9, v_newDecls_112_);
v___x_121_ = v_reuseFailAlloc_125_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lean_st_ref_set(v___y_99_, v___x_121_);
v___x_123_ = lean_box(0);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
}
v___jp_127_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_151_; 
v___x_136_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_82_);
v___x_137_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v___x_136_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_151_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_151_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_151_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
lean_inc_ref_n(v___y_134_, 2);
v___x_142_ = l_Lean_FileMap_toPosition(v___y_134_, v___y_131_);
lean_dec(v___y_131_);
v___x_143_ = l_Lean_FileMap_toPosition(v___y_134_, v___y_135_);
lean_dec(v___y_135_);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
v___x_145_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0));
if (v___y_132_ == 0)
{
lean_del_object(v___x_140_);
lean_dec_ref(v___y_128_);
v___y_91_ = v___y_129_;
v___y_92_ = v___x_144_;
v___y_93_ = v___x_142_;
v___y_94_ = v___y_130_;
v___y_95_ = v___x_145_;
v___y_96_ = v___y_133_;
v___y_97_ = v_a_138_;
v___y_98_ = v___y_87_;
v___y_99_ = v___y_88_;
goto v___jp_90_;
}
else
{
uint8_t v___x_146_; 
lean_inc(v_a_138_);
v___x_146_ = l_Lean_MessageData_hasTag(v___y_128_, v_a_138_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec_ref(v___x_144_);
lean_dec_ref(v___x_142_);
lean_dec(v_a_138_);
v___x_147_ = lean_box(0);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_147_);
v___x_149_ = v___x_140_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
else
{
lean_del_object(v___x_140_);
v___y_91_ = v___y_129_;
v___y_92_ = v___x_144_;
v___y_93_ = v___x_142_;
v___y_94_ = v___y_130_;
v___y_95_ = v___x_145_;
v___y_96_ = v___y_133_;
v___y_97_ = v_a_138_;
v___y_98_ = v___y_87_;
v___y_99_ = v___y_88_;
goto v___jp_90_;
}
}
}
}
v___jp_152_:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Syntax_getTailPos_x3f(v___y_156_, v___y_158_);
lean_dec(v___y_156_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_inc(v___y_160_);
v___y_128_ = v___y_153_;
v___y_129_ = v___y_154_;
v___y_130_ = v___y_155_;
v___y_131_ = v___y_160_;
v___y_132_ = v___y_159_;
v___y_133_ = v___y_158_;
v___y_134_ = v___y_157_;
v___y_135_ = v___y_160_;
goto v___jp_127_;
}
else
{
lean_object* v_val_162_; 
v_val_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_val_162_);
lean_dec_ref(v___x_161_);
v___y_128_ = v___y_153_;
v___y_129_ = v___y_154_;
v___y_130_ = v___y_155_;
v___y_131_ = v___y_160_;
v___y_132_ = v___y_159_;
v___y_133_ = v___y_158_;
v___y_134_ = v___y_157_;
v___y_135_ = v_val_162_;
goto v___jp_127_;
}
}
v___jp_163_:
{
lean_object* v_ref_171_; lean_object* v___x_172_; 
v_ref_171_ = l_Lean_replaceRef(v_ref_81_, v___y_169_);
v___x_172_ = l_Lean_Syntax_getPos_x3f(v_ref_171_, v___y_167_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v___x_173_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v___y_153_ = v___y_164_;
v___y_154_ = v___y_165_;
v___y_155_ = v___y_170_;
v___y_156_ = v_ref_171_;
v___y_157_ = v___y_168_;
v___y_158_ = v___y_167_;
v___y_159_ = v___y_166_;
v___y_160_ = v___x_173_;
goto v___jp_152_;
}
else
{
lean_object* v_val_174_; 
v_val_174_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_val_174_);
lean_dec_ref(v___x_172_);
v___y_153_ = v___y_164_;
v___y_154_ = v___y_165_;
v___y_155_ = v___y_170_;
v___y_156_ = v_ref_171_;
v___y_157_ = v___y_168_;
v___y_158_ = v___y_167_;
v___y_159_ = v___y_166_;
v___y_160_ = v_val_174_;
goto v___jp_152_;
}
}
v___jp_176_:
{
if (v___y_183_ == 0)
{
v___y_164_ = v___y_178_;
v___y_165_ = v___y_177_;
v___y_166_ = v___y_181_;
v___y_167_ = v___y_182_;
v___y_168_ = v___y_180_;
v___y_169_ = v___y_179_;
v___y_170_ = v_severity_83_;
goto v___jp_163_;
}
else
{
v___y_164_ = v___y_178_;
v___y_165_ = v___y_177_;
v___y_166_ = v___y_181_;
v___y_167_ = v___y_182_;
v___y_168_ = v___y_180_;
v___y_169_ = v___y_179_;
v___y_170_ = v___x_175_;
goto v___jp_163_;
}
}
v___jp_184_:
{
if (v___y_185_ == 0)
{
lean_object* v_fileName_186_; lean_object* v_fileMap_187_; lean_object* v_options_188_; lean_object* v_ref_189_; uint8_t v_suppressElabErrors_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___f_193_; uint8_t v___x_194_; uint8_t v___x_195_; 
v_fileName_186_ = lean_ctor_get(v___y_87_, 0);
v_fileMap_187_ = lean_ctor_get(v___y_87_, 1);
v_options_188_ = lean_ctor_get(v___y_87_, 2);
v_ref_189_ = lean_ctor_get(v___y_87_, 5);
v_suppressElabErrors_190_ = lean_ctor_get_uint8(v___y_87_, sizeof(void*)*14 + 1);
v___x_191_ = lean_box(v___y_185_);
v___x_192_ = lean_box(v_suppressElabErrors_190_);
v___f_193_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_193_, 0, v___x_191_);
lean_closure_set(v___f_193_, 1, v___x_192_);
v___x_194_ = 1;
v___x_195_ = l_Lean_instBEqMessageSeverity_beq(v_severity_83_, v___x_194_);
if (v___x_195_ == 0)
{
v___y_177_ = v_fileName_186_;
v___y_178_ = v___f_193_;
v___y_179_ = v_ref_189_;
v___y_180_ = v_fileMap_187_;
v___y_181_ = v_suppressElabErrors_190_;
v___y_182_ = v___y_185_;
v___y_183_ = v___x_195_;
goto v___jp_176_;
}
else
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = l_Lean_warningAsError;
v___x_197_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v_options_188_, v___x_196_);
v___y_177_ = v_fileName_186_;
v___y_178_ = v___f_193_;
v___y_179_ = v_ref_189_;
v___y_180_ = v_fileMap_187_;
v___y_181_ = v_suppressElabErrors_190_;
v___y_182_ = v___y_185_;
v___y_183_ = v___x_197_;
goto v___jp_176_;
}
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec_ref(v_msgData_82_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___boxed(lean_object* v_ref_202_, lean_object* v_msgData_203_, lean_object* v_severity_204_, lean_object* v_isSilent_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
uint8_t v_severity_boxed_211_; uint8_t v_isSilent_boxed_212_; lean_object* v_res_213_; 
v_severity_boxed_211_ = lean_unbox(v_severity_204_);
v_isSilent_boxed_212_ = lean_unbox(v_isSilent_205_);
v_res_213_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_202_, v_msgData_203_, v_severity_boxed_211_, v_isSilent_boxed_212_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v_ref_202_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(lean_object* v_ref_214_, lean_object* v_msgData_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
uint8_t v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; 
v___x_225_ = 1;
v___x_226_ = 0;
v___x_227_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_214_, v_msgData_215_, v___x_225_, v___x_226_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_227_;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(lean_object* v_stx_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v_options_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v_options_295_ = lean_ctor_get(v___y_252_, 2);
v___x_296_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_297_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v_options_295_, v___x_296_);
if (v___x_297_ == 0)
{
v___y_256_ = v___y_246_;
v___y_257_ = v___y_247_;
v___y_258_ = v___y_248_;
v___y_259_ = v___y_249_;
v___y_260_ = v___y_250_;
v___y_261_ = v___y_251_;
v___y_262_ = v___y_252_;
v___y_263_ = v___y_253_;
goto v___jp_255_;
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2);
v___x_299_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(v_stx_245_, v___x_298_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_dec_ref(v___x_299_);
v___y_256_ = v___y_246_;
v___y_257_ = v___y_247_;
v___y_258_ = v___y_248_;
v___y_259_ = v___y_249_;
v___y_260_ = v___y_250_;
v___y_261_ = v___y_251_;
v___y_262_ = v___y_252_;
v___y_263_ = v___y_253_;
goto v___jp_255_;
}
else
{
return v___x_299_;
}
}
v___jp_255_:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_257_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref(v___x_264_);
v___x_266_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_a_265_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_278_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_278_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_278_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
if (lean_obj_tag(v_a_267_) == 0)
{
lean_object* v___x_271_; lean_object* v___x_273_; 
lean_dec_ref(v_a_267_);
v___x_271_ = lean_box(0);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_271_);
v___x_273_ = v___x_269_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
else
{
lean_object* v_e_x27_275_; lean_object* v_proof_276_; lean_object* v___x_277_; 
lean_del_object(v___x_269_);
v_e_x27_275_ = lean_ctor_get(v_a_267_, 0);
lean_inc_ref(v_e_x27_275_);
v_proof_276_ = lean_ctor_get(v_a_267_, 1);
lean_inc_ref(v_proof_276_);
lean_dec_ref(v_a_267_);
v___x_277_ = l_Lean_Elab_Tactic_Conv_updateLhs(v_e_x27_275_, v_proof_276_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
return v___x_277_;
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_266_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_266_);
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
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_a_287_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_264_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_264_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed(lean_object* v_stx_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(v_stx_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v_stx_300_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv(lean_object* v_stx_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___f_321_; lean_object* v___x_322_; 
v___f_321_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed), 10, 1);
lean_closure_set(v___f_321_, 0, v_stx_311_);
v___x_322_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_321_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCbv___boxed(lean_object* v_stx_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Elab_Tactic_Conv_evalCbv(v_stx_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(lean_object* v_ref_334_, lean_object* v_msgData_335_, uint8_t v_severity_336_, uint8_t v_isSilent_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_334_, v_msgData_335_, v_severity_336_, v_isSilent_337_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___boxed(lean_object* v_ref_348_, lean_object* v_msgData_349_, lean_object* v_severity_350_, lean_object* v_isSilent_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v_severity_boxed_361_; uint8_t v_isSilent_boxed_362_; lean_object* v_res_363_; 
v_severity_boxed_361_ = lean_unbox(v_severity_350_);
v_isSilent_boxed_362_ = lean_unbox(v_isSilent_351_);
v_res_363_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(v_ref_348_, v_msgData_349_, v_severity_boxed_361_, v_isSilent_boxed_362_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v_ref_348_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1(){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_382_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4));
v___x_384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6));
v___x_385_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCbv___boxed), 10, 0);
v___x_386_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_382_, v___x_383_, v___x_384_, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___boxed(lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1();
return v_res_388_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
