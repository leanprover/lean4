// Lean compiler output
// Module: Lean.Elab.Tactic.Cbv
// Imports: public import Lean.Meta.Tactic.Cbv public import Lean.Meta.Tactic public import Lean.Elab.Tactic.Location
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
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_Cbv_cbv_warning;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "The `cbv` usage warning option is enabled. Disable it by setting `set_option cbv.warning false`."};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 5, 8, 249, 226, 109, 216, 194)}};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalCbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(39, 160, 233, 115, 188, 146, 109, 160)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 97, 15, 168, 224, 103, 171, 7)}};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Could not apply `of_decide_eq_true`"};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "of_decide_eq_true"};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 143, 142, 104, 169, 34, 63, 25)}};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "The `decide_cbv` usage warning option is enabled. Disable it by setting `set_option cbv.warning false`."};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decide_cbv"};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 35, 252, 51, 246, 88, 59, 166)}};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalDecideCbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(39, 160, 233, 115, 188, 146, 109, 160)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 23, 91, 61, 18, 243, 46, 172)}};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(uint8_t v_snd_15_, lean_object* v_fst_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_18_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v_a_27_; lean_object* v___x_28_; 
v_a_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_a_27_);
lean_dec_ref(v___x_26_);
v___x_28_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_a_27_, v_snd_15_, v_fst_16_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_a_31_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_a_29_);
lean_dec_ref(v___x_28_);
if (lean_obj_tag(v_a_29_) == 0)
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
v_a_31_ = v___x_42_;
goto v___jp_30_;
}
else
{
lean_object* v_val_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_val_43_ = lean_ctor_get(v_a_29_, 0);
lean_inc(v_val_43_);
lean_dec_ref(v_a_29_);
v___x_44_ = lean_box(0);
v___x_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_45_, 0, v_val_43_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v_a_31_ = v___x_45_;
goto v___jp_30_;
}
v___jp_30_:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_31_, v___y_18_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_40_ == 0)
{
lean_object* v_unused_41_; 
v_unused_41_ = lean_ctor_get(v___x_32_, 0);
lean_dec(v_unused_41_);
v___x_34_ = v___x_32_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_dec(v___x_32_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = lean_box(0);
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
else
{
return v___x_32_;
}
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_28_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_28_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_dec_ref(v_fst_16_);
v_a_54_ = lean_ctor_get(v___x_26_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_26_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_26_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed(lean_object* v_snd_62_, lean_object* v_fst_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
uint8_t v_snd_5764__boxed_73_; lean_object* v_res_74_; 
v_snd_5764__boxed_73_ = lean_unbox(v_snd_62_);
v_res_74_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(v_snd_5764__boxed_73_, v_fst_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2(lean_object* v_msgData_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; lean_object* v_env_82_; lean_object* v___x_83_; lean_object* v_mctx_84_; lean_object* v_lctx_85_; lean_object* v_options_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_81_ = lean_st_ref_get(v___y_79_);
v_env_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc_ref(v_env_82_);
lean_dec(v___x_81_);
v___x_83_ = lean_st_ref_get(v___y_77_);
v_mctx_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_mctx_84_);
lean_dec(v___x_83_);
v_lctx_85_ = lean_ctor_get(v___y_76_, 2);
v_options_86_ = lean_ctor_get(v___y_78_, 2);
lean_inc_ref(v_options_86_);
lean_inc_ref(v_lctx_85_);
v___x_87_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_87_, 0, v_env_82_);
lean_ctor_set(v___x_87_, 1, v_mctx_84_);
lean_ctor_set(v___x_87_, 2, v_lctx_85_);
lean_ctor_set(v___x_87_, 3, v_options_86_);
v___x_88_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_msgData_75_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2(v_msgData_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0(uint8_t v___y_105_, uint8_t v_suppressElabErrors_106_, lean_object* v_x_107_){
_start:
{
if (lean_obj_tag(v_x_107_) == 1)
{
lean_object* v_pre_108_; 
v_pre_108_ = lean_ctor_get(v_x_107_, 0);
switch(lean_obj_tag(v_pre_108_))
{
case 1:
{
lean_object* v_pre_109_; 
v_pre_109_ = lean_ctor_get(v_pre_108_, 0);
switch(lean_obj_tag(v_pre_109_))
{
case 0:
{
lean_object* v_str_110_; lean_object* v_str_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_str_110_ = lean_ctor_get(v_x_107_, 1);
v_str_111_ = lean_ctor_get(v_pre_108_, 1);
v___x_112_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0));
v___x_113_ = lean_string_dec_eq(v_str_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1));
v___x_115_ = lean_string_dec_eq(v_str_111_, v___x_114_);
if (v___x_115_ == 0)
{
return v___y_105_;
}
else
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2));
v___x_117_ = lean_string_dec_eq(v_str_110_, v___x_116_);
if (v___x_117_ == 0)
{
return v___y_105_;
}
else
{
return v_suppressElabErrors_106_;
}
}
}
else
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3));
v___x_119_ = lean_string_dec_eq(v_str_110_, v___x_118_);
if (v___x_119_ == 0)
{
return v___y_105_;
}
else
{
return v_suppressElabErrors_106_;
}
}
}
case 1:
{
lean_object* v_pre_120_; 
v_pre_120_ = lean_ctor_get(v_pre_109_, 0);
if (lean_obj_tag(v_pre_120_) == 0)
{
lean_object* v_str_121_; lean_object* v_str_122_; lean_object* v_str_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_str_121_ = lean_ctor_get(v_x_107_, 1);
v_str_122_ = lean_ctor_get(v_pre_108_, 1);
v_str_123_ = lean_ctor_get(v_pre_109_, 1);
v___x_124_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4));
v___x_125_ = lean_string_dec_eq(v_str_123_, v___x_124_);
if (v___x_125_ == 0)
{
return v___y_105_;
}
else
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5));
v___x_127_ = lean_string_dec_eq(v_str_122_, v___x_126_);
if (v___x_127_ == 0)
{
return v___y_105_;
}
else
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6));
v___x_129_ = lean_string_dec_eq(v_str_121_, v___x_128_);
if (v___x_129_ == 0)
{
return v___y_105_;
}
else
{
return v_suppressElabErrors_106_;
}
}
}
}
else
{
return v___y_105_;
}
}
default: 
{
return v___y_105_;
}
}
}
case 0:
{
lean_object* v_str_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v_str_130_ = lean_ctor_get(v_x_107_, 1);
v___x_131_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7));
v___x_132_ = lean_string_dec_eq(v_str_130_, v___x_131_);
if (v___x_132_ == 0)
{
return v___y_105_;
}
else
{
return v_suppressElabErrors_106_;
}
}
default: 
{
return v___y_105_;
}
}
}
else
{
return v___y_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_133_, lean_object* v_suppressElabErrors_134_, lean_object* v_x_135_){
_start:
{
uint8_t v___y_5912__boxed_136_; uint8_t v_suppressElabErrors_boxed_137_; uint8_t v_res_138_; lean_object* v_r_139_; 
v___y_5912__boxed_136_ = lean_unbox(v___y_133_);
v_suppressElabErrors_boxed_137_ = lean_unbox(v_suppressElabErrors_134_);
v_res_138_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0(v___y_5912__boxed_136_, v_suppressElabErrors_boxed_137_, v_x_135_);
lean_dec(v_x_135_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg(lean_object* v_ref_141_, lean_object* v_msgData_142_, uint8_t v_severity_143_, uint8_t v_isSilent_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
uint8_t v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_156_; uint8_t v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_187_; uint8_t v___y_188_; uint8_t v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_192_; uint8_t v___y_193_; lean_object* v___y_194_; lean_object* v___y_212_; uint8_t v___y_213_; uint8_t v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; uint8_t v___y_218_; lean_object* v___y_219_; lean_object* v___y_223_; uint8_t v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; uint8_t v___y_228_; uint8_t v___y_229_; uint8_t v___x_234_; uint8_t v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; uint8_t v___y_241_; uint8_t v___y_242_; uint8_t v___y_244_; uint8_t v___x_259_; 
v___x_234_ = 2;
v___x_259_ = l_Lean_instBEqMessageSeverity_beq(v_severity_143_, v___x_234_);
if (v___x_259_ == 0)
{
v___y_244_ = v___x_259_;
goto v___jp_243_;
}
else
{
uint8_t v___x_260_; 
lean_inc_ref(v_msgData_142_);
v___x_260_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_142_);
v___y_244_ = v___x_260_;
goto v___jp_243_;
}
v___jp_150_:
{
lean_object* v___x_160_; lean_object* v_currNamespace_161_; lean_object* v_openDecls_162_; lean_object* v_env_163_; lean_object* v_nextMacroScope_164_; lean_object* v_ngen_165_; lean_object* v_auxDeclNGen_166_; lean_object* v_traceState_167_; lean_object* v_cache_168_; lean_object* v_messages_169_; lean_object* v_infoState_170_; lean_object* v_snapshotTasks_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_185_; 
v___x_160_ = lean_st_ref_take(v___y_159_);
v_currNamespace_161_ = lean_ctor_get(v___y_158_, 6);
v_openDecls_162_ = lean_ctor_get(v___y_158_, 7);
v_env_163_ = lean_ctor_get(v___x_160_, 0);
v_nextMacroScope_164_ = lean_ctor_get(v___x_160_, 1);
v_ngen_165_ = lean_ctor_get(v___x_160_, 2);
v_auxDeclNGen_166_ = lean_ctor_get(v___x_160_, 3);
v_traceState_167_ = lean_ctor_get(v___x_160_, 4);
v_cache_168_ = lean_ctor_get(v___x_160_, 5);
v_messages_169_ = lean_ctor_get(v___x_160_, 6);
v_infoState_170_ = lean_ctor_get(v___x_160_, 7);
v_snapshotTasks_171_ = lean_ctor_get(v___x_160_, 8);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_185_ == 0)
{
v___x_173_ = v___x_160_;
v_isShared_174_ = v_isSharedCheck_185_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_snapshotTasks_171_);
lean_inc(v_infoState_170_);
lean_inc(v_messages_169_);
lean_inc(v_cache_168_);
lean_inc(v_traceState_167_);
lean_inc(v_auxDeclNGen_166_);
lean_inc(v_ngen_165_);
lean_inc(v_nextMacroScope_164_);
lean_inc(v_env_163_);
lean_dec(v___x_160_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_185_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
lean_inc(v_openDecls_162_);
lean_inc(v_currNamespace_161_);
v___x_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_175_, 0, v_currNamespace_161_);
lean_ctor_set(v___x_175_, 1, v_openDecls_162_);
v___x_176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___y_153_);
lean_inc_ref(v___y_154_);
lean_inc_ref(v___y_155_);
v___x_177_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_177_, 0, v___y_155_);
lean_ctor_set(v___x_177_, 1, v___y_156_);
lean_ctor_set(v___x_177_, 2, v___y_152_);
lean_ctor_set(v___x_177_, 3, v___y_154_);
lean_ctor_set(v___x_177_, 4, v___x_176_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*5, v___y_157_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*5 + 1, v___y_151_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*5 + 2, v_isSilent_144_);
v___x_178_ = l_Lean_MessageLog_add(v___x_177_, v_messages_169_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 6, v___x_178_);
v___x_180_ = v___x_173_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_env_163_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_nextMacroScope_164_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_ngen_165_);
lean_ctor_set(v_reuseFailAlloc_184_, 3, v_auxDeclNGen_166_);
lean_ctor_set(v_reuseFailAlloc_184_, 4, v_traceState_167_);
lean_ctor_set(v_reuseFailAlloc_184_, 5, v_cache_168_);
lean_ctor_set(v_reuseFailAlloc_184_, 6, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_184_, 7, v_infoState_170_);
lean_ctor_set(v_reuseFailAlloc_184_, 8, v_snapshotTasks_171_);
v___x_180_ = v_reuseFailAlloc_184_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_st_ref_set(v___y_159_, v___x_180_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
}
v___jp_186_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_210_; 
v___x_195_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_142_);
v___x_196_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2(v___x_195_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_210_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
lean_inc_ref_n(v___y_192_, 2);
v___x_201_ = l_Lean_FileMap_toPosition(v___y_192_, v___y_191_);
lean_dec(v___y_191_);
v___x_202_ = l_Lean_FileMap_toPosition(v___y_192_, v___y_194_);
lean_dec(v___y_194_);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
v___x_204_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___closed__0));
if (v___y_188_ == 0)
{
lean_del_object(v___x_199_);
lean_dec_ref(v___y_187_);
v___y_151_ = v___y_189_;
v___y_152_ = v___x_203_;
v___y_153_ = v_a_197_;
v___y_154_ = v___x_204_;
v___y_155_ = v___y_190_;
v___y_156_ = v___x_201_;
v___y_157_ = v___y_193_;
v___y_158_ = v___y_147_;
v___y_159_ = v___y_148_;
goto v___jp_150_;
}
else
{
uint8_t v___x_205_; 
lean_inc(v_a_197_);
v___x_205_ = l_Lean_MessageData_hasTag(v___y_187_, v_a_197_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_208_; 
lean_dec_ref(v___x_203_);
lean_dec_ref(v___x_201_);
lean_dec(v_a_197_);
v___x_206_ = lean_box(0);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_206_);
v___x_208_ = v___x_199_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
else
{
lean_del_object(v___x_199_);
v___y_151_ = v___y_189_;
v___y_152_ = v___x_203_;
v___y_153_ = v_a_197_;
v___y_154_ = v___x_204_;
v___y_155_ = v___y_190_;
v___y_156_ = v___x_201_;
v___y_157_ = v___y_193_;
v___y_158_ = v___y_147_;
v___y_159_ = v___y_148_;
goto v___jp_150_;
}
}
}
}
v___jp_211_:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Syntax_getTailPos_x3f(v___y_215_, v___y_218_);
lean_dec(v___y_215_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_inc(v___y_219_);
v___y_187_ = v___y_212_;
v___y_188_ = v___y_213_;
v___y_189_ = v___y_214_;
v___y_190_ = v___y_216_;
v___y_191_ = v___y_219_;
v___y_192_ = v___y_217_;
v___y_193_ = v___y_218_;
v___y_194_ = v___y_219_;
goto v___jp_186_;
}
else
{
lean_object* v_val_221_; 
v_val_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_221_);
lean_dec_ref(v___x_220_);
v___y_187_ = v___y_212_;
v___y_188_ = v___y_213_;
v___y_189_ = v___y_214_;
v___y_190_ = v___y_216_;
v___y_191_ = v___y_219_;
v___y_192_ = v___y_217_;
v___y_193_ = v___y_218_;
v___y_194_ = v_val_221_;
goto v___jp_186_;
}
}
v___jp_222_:
{
lean_object* v_ref_230_; lean_object* v___x_231_; 
v_ref_230_ = l_Lean_replaceRef(v_ref_141_, v___y_225_);
v___x_231_ = l_Lean_Syntax_getPos_x3f(v_ref_230_, v___y_228_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___y_212_ = v___y_223_;
v___y_213_ = v___y_224_;
v___y_214_ = v___y_229_;
v___y_215_ = v_ref_230_;
v___y_216_ = v___y_226_;
v___y_217_ = v___y_227_;
v___y_218_ = v___y_228_;
v___y_219_ = v___x_232_;
goto v___jp_211_;
}
else
{
lean_object* v_val_233_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_233_);
lean_dec_ref(v___x_231_);
v___y_212_ = v___y_223_;
v___y_213_ = v___y_224_;
v___y_214_ = v___y_229_;
v___y_215_ = v_ref_230_;
v___y_216_ = v___y_226_;
v___y_217_ = v___y_227_;
v___y_218_ = v___y_228_;
v___y_219_ = v_val_233_;
goto v___jp_211_;
}
}
v___jp_235_:
{
if (v___y_242_ == 0)
{
v___y_223_ = v___y_240_;
v___y_224_ = v___y_236_;
v___y_225_ = v___y_237_;
v___y_226_ = v___y_238_;
v___y_227_ = v___y_239_;
v___y_228_ = v___y_241_;
v___y_229_ = v_severity_143_;
goto v___jp_222_;
}
else
{
v___y_223_ = v___y_240_;
v___y_224_ = v___y_236_;
v___y_225_ = v___y_237_;
v___y_226_ = v___y_238_;
v___y_227_ = v___y_239_;
v___y_228_ = v___y_241_;
v___y_229_ = v___x_234_;
goto v___jp_222_;
}
}
v___jp_243_:
{
if (v___y_244_ == 0)
{
lean_object* v_fileName_245_; lean_object* v_fileMap_246_; lean_object* v_options_247_; lean_object* v_ref_248_; uint8_t v_suppressElabErrors_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___f_252_; uint8_t v___x_253_; uint8_t v___x_254_; 
v_fileName_245_ = lean_ctor_get(v___y_147_, 0);
v_fileMap_246_ = lean_ctor_get(v___y_147_, 1);
v_options_247_ = lean_ctor_get(v___y_147_, 2);
v_ref_248_ = lean_ctor_get(v___y_147_, 5);
v_suppressElabErrors_249_ = lean_ctor_get_uint8(v___y_147_, sizeof(void*)*14 + 1);
v___x_250_ = lean_box(v___y_244_);
v___x_251_ = lean_box(v_suppressElabErrors_249_);
v___f_252_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_252_, 0, v___x_250_);
lean_closure_set(v___f_252_, 1, v___x_251_);
v___x_253_ = 1;
v___x_254_ = l_Lean_instBEqMessageSeverity_beq(v_severity_143_, v___x_253_);
if (v___x_254_ == 0)
{
v___y_236_ = v_suppressElabErrors_249_;
v___y_237_ = v_ref_248_;
v___y_238_ = v_fileName_245_;
v___y_239_ = v_fileMap_246_;
v___y_240_ = v___f_252_;
v___y_241_ = v___y_244_;
v___y_242_ = v___x_254_;
goto v___jp_235_;
}
else
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = l_Lean_warningAsError;
v___x_256_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(v_options_247_, v___x_255_);
v___y_236_ = v_suppressElabErrors_249_;
v___y_237_ = v_ref_248_;
v___y_238_ = v_fileName_245_;
v___y_239_ = v_fileMap_246_;
v___y_240_ = v___f_252_;
v___y_241_ = v___y_244_;
v___y_242_ = v___x_256_;
goto v___jp_235_;
}
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref(v_msgData_142_);
v___x_257_ = lean_box(0);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg___boxed(lean_object* v_ref_261_, lean_object* v_msgData_262_, lean_object* v_severity_263_, lean_object* v_isSilent_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
uint8_t v_severity_boxed_270_; uint8_t v_isSilent_boxed_271_; lean_object* v_res_272_; 
v_severity_boxed_270_ = lean_unbox(v_severity_263_);
v_isSilent_boxed_271_ = lean_unbox(v_isSilent_264_);
v_res_272_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg(v_ref_261_, v_msgData_262_, v_severity_boxed_270_, v_isSilent_boxed_271_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v_ref_261_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(lean_object* v_ref_273_, lean_object* v_msgData_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
uint8_t v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; 
v___x_284_ = 1;
v___x_285_ = 0;
v___x_286_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg(v_ref_273_, v_msgData_274_, v___x_284_, v___x_285_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1___boxed(lean_object* v_ref_287_, lean_object* v_msgData_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_ref_287_, v_msgData_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v_ref_287_);
return v_res_298_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__1));
v___x_303_ = l_Lean_MessageData_ofFormat(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(lean_object* v_stx_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_fst_315_; uint8_t v_snd_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v_options_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v_options_373_ = lean_ctor_get(v___y_311_, 2);
v___x_374_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_375_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(v_options_373_, v___x_374_);
if (v___x_375_ == 0)
{
v___y_329_ = v___y_305_;
v___y_330_ = v___y_306_;
v___y_331_ = v___y_307_;
v___y_332_ = v___y_308_;
v___y_333_ = v___y_309_;
v___y_334_ = v___y_310_;
v___y_335_ = v___y_311_;
v___y_336_ = v___y_312_;
goto v___jp_328_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2, &l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___closed__2);
v___x_377_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_stx_304_, v___x_376_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_dec_ref(v___x_377_);
v___y_329_ = v___y_305_;
v___y_330_ = v___y_306_;
v___y_331_ = v___y_307_;
v___y_332_ = v___y_308_;
v___y_333_ = v___y_309_;
v___y_334_ = v___y_310_;
v___y_335_ = v___y_311_;
v___y_336_ = v___y_312_;
goto v___jp_328_;
}
else
{
return v___x_377_;
}
}
v___jp_314_:
{
lean_object* v___x_325_; lean_object* v___f_326_; lean_object* v___x_327_; 
v___x_325_ = lean_box(v_snd_316_);
v___f_326_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed), 11, 2);
lean_closure_set(v___f_326_, 0, v___x_325_);
lean_closure_set(v___f_326_, 1, v_fst_315_);
v___x_327_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_326_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_327_;
}
v___jp_328_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = l_Lean_Syntax_getArg(v_stx_304_, v___x_337_);
v___x_339_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_338_);
lean_dec(v___x_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_330_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref(v___x_340_);
v___x_342_ = l_Lean_MVarId_getNondepPropHyps(v_a_341_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; uint8_t v___x_344_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref(v___x_342_);
v___x_344_ = 1;
v_fst_315_ = v_a_343_;
v_snd_316_ = v___x_344_;
v___y_317_ = v___y_329_;
v___y_318_ = v___y_330_;
v___y_319_ = v___y_331_;
v___y_320_ = v___y_332_;
v___y_321_ = v___y_333_;
v___y_322_ = v___y_334_;
v___y_323_ = v___y_335_;
v___y_324_ = v___y_336_;
goto v___jp_314_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_345_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_342_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_a_353_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_340_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_340_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_hypotheses_361_; uint8_t v_type_362_; lean_object* v___x_363_; 
v_hypotheses_361_ = lean_ctor_get(v___x_339_, 0);
lean_inc_ref(v_hypotheses_361_);
v_type_362_ = lean_ctor_get_uint8(v___x_339_, sizeof(void*)*1);
lean_dec_ref(v___x_339_);
v___x_363_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_361_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref(v___x_363_);
v_fst_315_ = v_a_364_;
v_snd_316_ = v_type_362_;
v___y_317_ = v___y_329_;
v___y_318_ = v___y_330_;
v___y_319_ = v___y_331_;
v___y_320_ = v___y_332_;
v___y_321_ = v___y_333_;
v___y_322_ = v___y_334_;
v___y_323_ = v___y_335_;
v___y_324_ = v___y_336_;
goto v___jp_314_;
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
v_a_365_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_363_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_363_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed(lean_object* v_stx_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(v_stx_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v_stx_378_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv(lean_object* v_stx_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___f_399_; lean_object* v___x_400_; 
v___f_399_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed), 10, 1);
lean_closure_set(v___f_399_, 0, v_stx_389_);
v___x_400_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_399_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___boxed(lean_object* v_stx_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_Tactic_Cbv_evalCbv(v_stx_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1(lean_object* v_ref_412_, lean_object* v_msgData_413_, uint8_t v_severity_414_, uint8_t v_isSilent_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___redArg(v_ref_412_, v_msgData_413_, v_severity_414_, v_isSilent_415_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1___boxed(lean_object* v_ref_426_, lean_object* v_msgData_427_, lean_object* v_severity_428_, lean_object* v_isSilent_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v_severity_boxed_439_; uint8_t v_isSilent_boxed_440_; lean_object* v_res_441_; 
v_severity_boxed_439_ = lean_unbox(v_severity_428_);
v_isSilent_boxed_440_ = lean_unbox(v_isSilent_429_);
v_res_441_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1(v_ref_426_, v_msgData_427_, v_severity_boxed_439_, v_isSilent_boxed_440_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v_ref_426_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1(){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_459_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3));
v___x_461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6));
v___x_462_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___boxed), 10, 0);
v___x_463_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_459_, v___x_460_, v___x_461_, v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___boxed(lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
return v_res_465_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_box(0);
v___x_467_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___closed__0);
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___boxed(lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg();
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(lean_object* v_00_u03b1_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg();
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___boxed(lean_object* v_00_u03b1_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(v_00_u03b1_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(lean_object* v_msg_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_ref_502_; lean_object* v___x_503_; lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
v_ref_502_ = lean_ctor_get(v___y_499_, 5);
v___x_503_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__1_spec__2(v_msg_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v___x_503_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
lean_inc(v_ref_502_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_ref_502_);
lean_ctor_set(v___x_508_, 1, v_a_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 1);
lean_ctor_set(v___x_506_, 0, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___boxed(lean_object* v_msg_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(v_msg_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_519_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0));
v___x_522_ = l_Lean_stringToMessageData(v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(lean_object* v_x_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1, &l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1);
v___x_530_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(v___x_529_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___boxed(lean_object* v_x_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(v_x_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v_x_531_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(uint8_t v___x_541_, lean_object* v___f_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___y_553_; lean_object* v___x_565_; 
v___x_565_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_544_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; uint8_t v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref(v___x_565_);
v___x_567_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1));
v___x_568_ = 0;
v___x_569_ = 0;
v___x_570_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_570_, 0, v___x_568_);
lean_ctor_set_uint8(v___x_570_, 1, v___x_541_);
lean_ctor_set_uint8(v___x_570_, 2, v___x_569_);
lean_ctor_set_uint8(v___x_570_, 3, v___x_541_);
v___x_571_ = l_Lean_MVarId_applyConst(v_a_566_, v___x_567_, v___x_570_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref(v___x_571_);
if (lean_obj_tag(v_a_572_) == 1)
{
lean_object* v_tail_573_; 
v_tail_573_ = lean_ctor_get(v_a_572_, 1);
if (lean_obj_tag(v_tail_573_) == 0)
{
lean_object* v_head_574_; lean_object* v___x_575_; 
lean_dec_ref(v___f_542_);
v_head_574_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_head_574_);
lean_dec_ref(v_a_572_);
v___x_575_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_head_574_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
v___y_553_ = v___x_575_;
goto v___jp_552_;
}
else
{
lean_object* v___x_576_; 
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
v___x_576_ = lean_apply_6(v___f_542_, v_a_572_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, lean_box(0));
v___y_553_ = v___x_576_;
goto v___jp_552_;
}
}
else
{
lean_object* v___x_577_; 
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
v___x_577_ = lean_apply_6(v___f_542_, v_a_572_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, lean_box(0));
v___y_553_ = v___x_577_;
goto v___jp_552_;
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec_ref(v___f_542_);
v_a_578_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_571_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_571_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec_ref(v___f_542_);
v_a_586_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_565_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_565_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
v___jp_552_:
{
if (lean_obj_tag(v___y_553_) == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v___y_553_);
v___x_554_ = lean_box(0);
v___x_555_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_554_, v___y_544_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v___x_555_, 0);
lean_dec(v_unused_564_);
v___x_557_ = v___x_555_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_dec(v___x_555_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_559_ = lean_box(0);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
return v___x_555_;
}
}
else
{
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v___y_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed(lean_object* v___x_594_, lean_object* v___f_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
uint8_t v___x_2213__boxed_605_; lean_object* v_res_606_; 
v___x_2213__boxed_605_ = lean_unbox(v___x_594_);
v_res_606_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(v___x_2213__boxed_605_, v___f_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_606_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1));
v___x_611_ = l_Lean_MessageData_ofFormat(v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(lean_object* v___f_612_, lean_object* v_stx_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_options_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_options_623_ = lean_ctor_get(v___y_620_, 2);
v___x_624_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_625_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(v_options_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_612_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2, &l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2);
v___x_628_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_stx_613_, v___x_627_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v___x_629_; 
lean_dec_ref(v___x_628_);
v___x_629_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_612_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_629_;
}
else
{
lean_dec_ref(v___f_612_);
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed(lean_object* v___f_630_, lean_object* v_stx_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(v___f_630_, v_stx_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v_stx_631_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv(lean_object* v_stx_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1));
lean_inc(v_stx_649_);
v___x_660_ = l_Lean_Syntax_isOfKind(v_stx_649_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec(v_stx_649_);
v___x_661_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg();
return v___x_661_;
}
else
{
lean_object* v___f_662_; lean_object* v___x_663_; lean_object* v___f_664_; lean_object* v___f_665_; lean_object* v___x_666_; 
v___f_662_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2));
v___x_663_ = lean_box(v___x_660_);
v___f_664_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed), 11, 2);
lean_closure_set(v___f_664_, 0, v___x_663_);
lean_closure_set(v___f_664_, 1, v___f_662_);
v___f_665_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed), 11, 2);
lean_closure_set(v___f_665_, 0, v___f_664_);
lean_closure_set(v___f_665_, 1, v_stx_649_);
v___x_666_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_665_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed(lean_object* v_stx_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv(v_stx_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(lean_object* v_00_u03b1_678_, lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(v_msg_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___boxed(lean_object* v_00_u03b1_686_, lean_object* v_msg_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(v_00_u03b1_686_, v_msg_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1(){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_702_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_703_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1));
v___x_704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1));
v___x_705_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed), 10, 0);
v___x_706_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_702_, v___x_703_, v___x_704_, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___boxed(lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
return v_res_708_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Cbv(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Cbv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Cbv(builtin);
}
#ifdef __cplusplus
}
#endif
