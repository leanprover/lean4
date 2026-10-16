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
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_Cbv_cbv_warning;
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Tactic_Cbv_cbvHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Cbv_cbvTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_cbvTarget___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "`cbv` failed"};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "The `cbv` usage warning option is enabled. Disable it by setting `set_option cbv.warning false`."};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Cbv_evalCbv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalCbv___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 5, 8, 249, 226, 109, 216, 194)}};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalCbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(39, 160, 233, 115, 188, 146, 109, 160)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 97, 15, 168, 224, 103, 171, 7)}};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 35, 252, 51, 246, 88, 59, 166)}};
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalDecideCbv"};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(39, 160, 233, 115, 188, 146, 109, 160)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 23, 91, 61, 18, 243, 46, 172)}};
static const lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0(lean_object* v_fvarId_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_a_12_; lean_object* v___x_23_; 
v___x_23_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_3_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_25_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_a_24_);
lean_dec_ref_known(v___x_23_, 1);
v___x_25_ = l_Lean_Meta_Tactic_Cbv_cbvHyp(v_a_24_, v_fvarId_1_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v_a_26_; 
v_a_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_a_26_);
lean_dec_ref_known(v___x_25_, 1);
if (lean_obj_tag(v_a_26_) == 0)
{
lean_object* v___x_27_; 
v___x_27_ = lean_box(0);
v_a_12_ = v___x_27_;
goto v___jp_11_;
}
else
{
lean_object* v_val_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_val_28_ = lean_ctor_get(v_a_26_, 0);
lean_inc(v_val_28_);
lean_dec_ref_known(v_a_26_, 1);
v___x_29_ = lean_box(0);
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v_val_28_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v_a_12_ = v___x_30_;
goto v___jp_11_;
}
}
else
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_25_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_25_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_25_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
lean_dec(v_fvarId_1_);
v_a_39_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_23_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_23_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
v___jp_11_:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_box(0);
v___x_14_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_12_, v___y_3_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_21_ == 0)
{
lean_object* v_unused_22_; 
v_unused_22_ = lean_ctor_get(v___x_14_, 0);
lean_dec(v_unused_22_);
v___x_16_ = v___x_14_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_dec(v___x_14_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v___x_13_);
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_13_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
else
{
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0___boxed(lean_object* v_fvarId_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0(v_fvarId_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(lean_object* v_fvarId_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___f_68_; lean_object* v___x_69_; 
v___f_68_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0___boxed), 10, 1);
lean_closure_set(v___f_68_, 0, v_fvarId_58_);
v___x_69_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_68_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___boxed(lean_object* v_fvarId_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0(lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_a_91_; lean_object* v___x_102_; 
v___x_102_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_82_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_104_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
v___x_104_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_a_103_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
if (lean_obj_tag(v_a_105_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(0);
v_a_91_ = v___x_106_;
goto v___jp_90_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_val_107_ = lean_ctor_get(v_a_105_, 0);
lean_inc(v_val_107_);
lean_dec_ref_known(v_a_105_, 1);
v___x_108_ = lean_box(0);
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v_val_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v_a_91_ = v___x_109_;
goto v___jp_90_;
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_a_110_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_104_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_104_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_a_118_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_102_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_102_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_box(0);
v___x_93_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_91_, v___y_82_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_93_, 0);
lean_dec(v_unused_101_);
v___x_95_ = v___x_93_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_dec(v___x_93_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_92_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_92_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0___boxed(lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0(v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget(lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___f_146_; lean_object* v___x_147_; 
v___f_146_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_cbvTarget___closed__0));
v___x_147_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_146_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget___boxed(lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Elab_Tactic_Cbv_cbvTarget(v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
return v_res_157_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(lean_object* v_opts_158_, lean_object* v_opt_159_){
_start:
{
lean_object* v_name_160_; lean_object* v_defValue_161_; lean_object* v_map_162_; lean_object* v___x_163_; 
v_name_160_ = lean_ctor_get(v_opt_159_, 0);
v_defValue_161_ = lean_ctor_get(v_opt_159_, 1);
v_map_162_ = lean_ctor_get(v_opts_158_, 0);
v___x_163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_162_, v_name_160_);
if (lean_obj_tag(v___x_163_) == 0)
{
uint8_t v___x_164_; 
v___x_164_ = lean_unbox(v_defValue_161_);
return v___x_164_;
}
else
{
lean_object* v_val_165_; 
v_val_165_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v___x_163_, 1);
if (lean_obj_tag(v_val_165_) == 1)
{
uint8_t v_v_166_; 
v_v_166_ = lean_ctor_get_uint8(v_val_165_, 0);
lean_dec_ref_known(v_val_165_, 0);
return v_v_166_;
}
else
{
uint8_t v___x_167_; 
lean_dec(v_val_165_);
v___x_167_ = lean_unbox(v_defValue_161_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2___boxed(lean_object* v_opts_168_, lean_object* v_opt_169_){
_start:
{
uint8_t v_res_170_; lean_object* v_r_171_; 
v_res_170_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v_opts_168_, v_opt_169_);
lean_dec_ref(v_opt_169_);
lean_dec_ref(v_opts_168_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(lean_object* v_msgData_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; lean_object* v_env_179_; uint8_t v___x_180_; lean_object* v_env_181_; lean_object* v___x_182_; lean_object* v_toCold_183_; lean_object* v_mctx_184_; lean_object* v_lctx_185_; lean_object* v_options_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_178_ = lean_st_ref_get(v___y_176_);
v_env_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc_ref(v_env_179_);
lean_dec(v___x_178_);
v___x_180_ = 0;
v_env_181_ = l_Lean_Environment_setRecordingDeps(v_env_179_, v___x_180_);
v___x_182_ = lean_st_ref_get(v___y_174_);
v_toCold_183_ = lean_ctor_get(v___y_175_, 0);
v_mctx_184_ = lean_ctor_get(v___x_182_, 0);
lean_inc_ref(v_mctx_184_);
lean_dec(v___x_182_);
v_lctx_185_ = lean_ctor_get(v___y_173_, 2);
v_options_186_ = lean_ctor_get(v_toCold_183_, 2);
lean_inc_ref(v_options_186_);
lean_inc_ref(v_lctx_185_);
v___x_187_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_187_, 0, v_env_181_);
lean_ctor_set(v___x_187_, 1, v_mctx_184_);
lean_ctor_set(v___x_187_, 2, v_lctx_185_);
lean_ctor_set(v___x_187_, 3, v_options_186_);
v___x_188_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_msgData_172_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0___boxed(lean_object* v_msgData_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msgData_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(lean_object* v_msg_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_ref_203_; lean_object* v___x_204_; lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
v_ref_203_ = lean_ctor_get(v___y_200_, 2);
v___x_204_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msg_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_213_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
lean_inc(v_ref_203_);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v_ref_203_);
lean_ctor_set(v___x_209_, 1, v_a_205_);
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 1);
lean_ctor_set(v___x_207_, 0, v___x_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg___boxed(lean_object* v_msg_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v_msg_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
return v_res_220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__0));
v___x_223_ = l_Lean_stringToMessageData(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(lean_object* v_x_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1, &l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1);
v___x_235_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v___x_234_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed(lean_object* v_x_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(v_x_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v_x_236_);
return v_res_246_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(lean_object* v_a_247_, lean_object* v_as_248_, size_t v_i_249_, size_t v_stop_250_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = lean_usize_dec_eq(v_i_249_, v_stop_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_array_uget_borrowed(v_as_248_, v_i_249_);
v___x_253_ = l_Lean_instBEqFVarId_beq(v_a_247_, v___x_252_);
if (v___x_253_ == 0)
{
size_t v___x_254_; size_t v___x_255_; 
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_i_249_, v___x_254_);
v_i_249_ = v___x_255_;
goto _start;
}
else
{
return v___x_253_;
}
}
else
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2___boxed(lean_object* v_a_258_, lean_object* v_as_259_, lean_object* v_i_260_, lean_object* v_stop_261_){
_start:
{
size_t v_i_boxed_262_; size_t v_stop_boxed_263_; uint8_t v_res_264_; lean_object* v_r_265_; 
v_i_boxed_262_ = lean_unbox_usize(v_i_260_);
lean_dec(v_i_260_);
v_stop_boxed_263_ = lean_unbox_usize(v_stop_261_);
lean_dec(v_stop_261_);
v_res_264_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(v_a_258_, v_as_259_, v_i_boxed_262_, v_stop_boxed_263_);
lean_dec_ref(v_as_259_);
lean_dec(v_a_258_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(lean_object* v_as_266_, lean_object* v_a_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_array_get_size(v_as_266_);
v___x_270_ = lean_nat_dec_lt(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
return v___x_270_;
}
else
{
size_t v___x_271_; size_t v___x_272_; uint8_t v___x_273_; 
v___x_271_ = ((size_t)0ULL);
v___x_272_ = lean_usize_of_nat(v___x_269_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(v_a_267_, v_as_266_, v___x_271_, v___x_272_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1___boxed(lean_object* v_as_274_, lean_object* v_a_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_as_274_, v_a_275_);
lean_dec(v_a_275_);
lean_dec_ref(v_as_274_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(lean_object* v_wildcardHyps_x3f_278_, lean_object* v_fvarId_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
if (lean_obj_tag(v_wildcardHyps_x3f_278_) == 1)
{
lean_object* v_val_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_299_; 
v_val_289_ = lean_ctor_get(v_wildcardHyps_x3f_278_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_wildcardHyps_x3f_278_);
if (v_isSharedCheck_299_ == 0)
{
v___x_291_ = v_wildcardHyps_x3f_278_;
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_val_289_);
lean_dec(v_wildcardHyps_x3f_278_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_299_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
uint8_t v___x_293_; 
v___x_293_ = l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_val_289_, v_fvarId_279_);
lean_dec(v_val_289_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_296_; 
lean_dec(v_fvarId_279_);
v___x_294_ = lean_box(0);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 0);
lean_ctor_set(v___x_291_, 0, v___x_294_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
else
{
lean_object* v___x_298_; 
lean_del_object(v___x_291_);
v___x_298_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
return v___x_298_;
}
}
}
else
{
lean_object* v___x_300_; 
lean_dec(v_wildcardHyps_x3f_278_);
v___x_300_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed(lean_object* v_wildcardHyps_x3f_301_, lean_object* v_fvarId_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(v_wildcardHyps_x3f_301_, v_fvarId_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_312_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(uint8_t v_suppressElabErrors_321_, lean_object* v_x_322_){
_start:
{
if (lean_obj_tag(v_x_322_) == 1)
{
lean_object* v_pre_323_; 
v_pre_323_ = lean_ctor_get(v_x_322_, 0);
switch(lean_obj_tag(v_pre_323_))
{
case 1:
{
lean_object* v_pre_324_; 
v_pre_324_ = lean_ctor_get(v_pre_323_, 0);
switch(lean_obj_tag(v_pre_324_))
{
case 0:
{
lean_object* v_str_325_; lean_object* v_str_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_str_325_ = lean_ctor_get(v_x_322_, 1);
v_str_326_ = lean_ctor_get(v_pre_323_, 1);
v___x_327_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__0));
v___x_328_ = lean_string_dec_eq(v_str_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1));
v___x_330_ = lean_string_dec_eq(v_str_326_, v___x_329_);
if (v___x_330_ == 0)
{
return v___x_330_;
}
else
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__2));
v___x_332_ = lean_string_dec_eq(v_str_325_, v___x_331_);
if (v___x_332_ == 0)
{
return v___x_332_;
}
else
{
return v_suppressElabErrors_321_;
}
}
}
else
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__3));
v___x_334_ = lean_string_dec_eq(v_str_325_, v___x_333_);
if (v___x_334_ == 0)
{
return v___x_334_;
}
else
{
return v_suppressElabErrors_321_;
}
}
}
case 1:
{
lean_object* v_pre_335_; 
v_pre_335_ = lean_ctor_get(v_pre_324_, 0);
if (lean_obj_tag(v_pre_335_) == 0)
{
lean_object* v_str_336_; lean_object* v_str_337_; lean_object* v_str_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_str_336_ = lean_ctor_get(v_x_322_, 1);
v_str_337_ = lean_ctor_get(v_pre_323_, 1);
v_str_338_ = lean_ctor_get(v_pre_324_, 1);
v___x_339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__4));
v___x_340_ = lean_string_dec_eq(v_str_338_, v___x_339_);
if (v___x_340_ == 0)
{
return v___x_340_;
}
else
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__5));
v___x_342_ = lean_string_dec_eq(v_str_337_, v___x_341_);
if (v___x_342_ == 0)
{
return v___x_342_;
}
else
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__6));
v___x_344_ = lean_string_dec_eq(v_str_336_, v___x_343_);
if (v___x_344_ == 0)
{
return v___x_344_;
}
else
{
return v_suppressElabErrors_321_;
}
}
}
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 0;
return v___x_345_;
}
}
default: 
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
}
}
case 0:
{
lean_object* v_str_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_str_347_ = lean_ctor_get(v_x_322_, 1);
v___x_348_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__7));
v___x_349_ = lean_string_dec_eq(v_str_347_, v___x_348_);
if (v___x_349_ == 0)
{
return v___x_349_;
}
else
{
return v_suppressElabErrors_321_;
}
}
default: 
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
}
}
else
{
uint8_t v___x_351_; 
v___x_351_ = 0;
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_352_, lean_object* v_x_353_){
_start:
{
uint8_t v_suppressElabErrors_boxed_354_; uint8_t v_res_355_; lean_object* v_r_356_; 
v_suppressElabErrors_boxed_354_ = lean_unbox(v_suppressElabErrors_352_);
v_res_355_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(v_suppressElabErrors_boxed_354_, v_x_353_);
lean_dec(v_x_353_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(lean_object* v_ref_358_, lean_object* v_msgData_359_, uint8_t v_severity_360_, uint8_t v_isSilent_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; uint8_t v___y_372_; lean_object* v___y_373_; uint8_t v___y_374_; lean_object* v_toCold_375_; lean_object* v___y_376_; lean_object* v___y_405_; lean_object* v___y_406_; uint8_t v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; uint8_t v___y_410_; uint8_t v___y_411_; lean_object* v___y_412_; uint8_t v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; uint8_t v___y_436_; uint8_t v___y_437_; lean_object* v___y_438_; uint8_t v___y_442_; uint8_t v___y_443_; uint8_t v___x_453_; uint8_t v___y_455_; uint8_t v___x_461_; 
v___x_453_ = 2;
v___x_461_ = l_Lean_instBEqMessageSeverity_beq(v_severity_360_, v___x_453_);
if (v___x_461_ == 0)
{
v___y_455_ = v___x_461_;
goto v___jp_454_;
}
else
{
uint8_t v___x_462_; 
lean_inc_ref(v_msgData_359_);
v___x_462_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_359_);
if (v___x_462_ == 0)
{
v___y_455_ = v___x_462_;
goto v___jp_454_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec_ref(v_msgData_359_);
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
}
v___jp_367_:
{
lean_object* v_currNamespace_377_; lean_object* v_openDecls_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v_env_383_; lean_object* v_nextMacroScope_384_; lean_object* v_ngen_385_; lean_object* v_auxDeclNGen_386_; lean_object* v_traceState_387_; lean_object* v_cache_388_; lean_object* v_recordedDeps_389_; lean_object* v_messages_390_; lean_object* v_infoState_391_; lean_object* v_snapshotTasks_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_403_; 
v_currNamespace_377_ = lean_ctor_get(v_toCold_375_, 4);
v_openDecls_378_ = lean_ctor_get(v_toCold_375_, 5);
lean_inc(v_openDecls_378_);
lean_inc(v_currNamespace_377_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_currNamespace_377_);
lean_ctor_set(v___x_379_, 1, v_openDecls_378_);
v___x_380_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___y_371_);
lean_inc_ref(v___y_369_);
lean_inc_ref(v___y_368_);
v___x_381_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_381_, 0, v___y_368_);
lean_ctor_set(v___x_381_, 1, v___y_370_);
lean_ctor_set(v___x_381_, 2, v___y_373_);
lean_ctor_set(v___x_381_, 3, v___y_369_);
lean_ctor_set(v___x_381_, 4, v___x_380_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*5, v___y_374_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*5 + 1, v___y_372_);
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*5 + 2, v_isSilent_361_);
v___x_382_ = lean_st_ref_take(v___y_376_);
v_env_383_ = lean_ctor_get(v___x_382_, 0);
v_nextMacroScope_384_ = lean_ctor_get(v___x_382_, 1);
v_ngen_385_ = lean_ctor_get(v___x_382_, 2);
v_auxDeclNGen_386_ = lean_ctor_get(v___x_382_, 3);
v_traceState_387_ = lean_ctor_get(v___x_382_, 4);
v_cache_388_ = lean_ctor_get(v___x_382_, 5);
v_recordedDeps_389_ = lean_ctor_get(v___x_382_, 6);
v_messages_390_ = lean_ctor_get(v___x_382_, 7);
v_infoState_391_ = lean_ctor_get(v___x_382_, 8);
v_snapshotTasks_392_ = lean_ctor_get(v___x_382_, 9);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_403_ == 0)
{
v___x_394_ = v___x_382_;
v_isShared_395_ = v_isSharedCheck_403_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_snapshotTasks_392_);
lean_inc(v_infoState_391_);
lean_inc(v_messages_390_);
lean_inc(v_recordedDeps_389_);
lean_inc(v_cache_388_);
lean_inc(v_traceState_387_);
lean_inc(v_auxDeclNGen_386_);
lean_inc(v_ngen_385_);
lean_inc(v_nextMacroScope_384_);
lean_inc(v_env_383_);
lean_dec(v___x_382_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_403_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = lean_box(0);
v___x_397_ = l_Lean_MessageLog_add(v___x_381_, v_messages_390_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 7, v___x_397_);
v___x_399_ = v___x_394_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_env_383_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_nextMacroScope_384_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_ngen_385_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_auxDeclNGen_386_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_traceState_387_);
lean_ctor_set(v_reuseFailAlloc_402_, 5, v_cache_388_);
lean_ctor_set(v_reuseFailAlloc_402_, 6, v_recordedDeps_389_);
lean_ctor_set(v_reuseFailAlloc_402_, 7, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_402_, 8, v_infoState_391_);
lean_ctor_set(v_reuseFailAlloc_402_, 9, v_snapshotTasks_392_);
v___x_399_ = v_reuseFailAlloc_402_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_st_ref_put(v___y_376_, v___x_399_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_396_);
return v___x_401_;
}
}
}
v___jp_404_:
{
lean_object* v_fileName_413_; lean_object* v_fileMap_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_430_; 
v_fileName_413_ = lean_ctor_get(v___y_408_, 0);
v_fileMap_414_ = lean_ctor_get(v___y_408_, 1);
v___x_415_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_359_);
v___x_416_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v___x_415_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_430_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_430_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_inc_ref_n(v_fileMap_414_, 2);
v___x_421_ = l_Lean_FileMap_toPosition(v_fileMap_414_, v___y_409_);
lean_dec(v___y_409_);
v___x_422_ = l_Lean_FileMap_toPosition(v_fileMap_414_, v___y_412_);
lean_dec(v___y_412_);
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
v___x_424_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___closed__0));
if (v___y_407_ == 0)
{
lean_del_object(v___x_419_);
lean_dec_ref(v___y_405_);
v___y_368_ = v_fileName_413_;
v___y_369_ = v___x_424_;
v___y_370_ = v___x_421_;
v___y_371_ = v_a_417_;
v___y_372_ = v___y_410_;
v___y_373_ = v___x_423_;
v___y_374_ = v___y_411_;
v_toCold_375_ = v___y_406_;
v___y_376_ = v___y_365_;
goto v___jp_367_;
}
else
{
uint8_t v___x_425_; 
lean_inc(v_a_417_);
v___x_425_ = l_Lean_MessageData_hasTag(v___y_405_, v_a_417_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_428_; 
lean_dec_ref_known(v___x_423_, 1);
lean_dec_ref(v___x_421_);
lean_dec(v_a_417_);
v___x_426_ = lean_box(0);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_426_);
v___x_428_ = v___x_419_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
else
{
lean_del_object(v___x_419_);
v___y_368_ = v_fileName_413_;
v___y_369_ = v___x_424_;
v___y_370_ = v___x_421_;
v___y_371_ = v_a_417_;
v___y_372_ = v___y_410_;
v___y_373_ = v___x_423_;
v___y_374_ = v___y_411_;
v_toCold_375_ = v___y_406_;
v___y_376_ = v___y_365_;
goto v___jp_367_;
}
}
}
}
v___jp_431_:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Syntax_getTailPos_x3f(v___y_435_, v___y_437_);
lean_dec(v___y_435_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_inc(v___y_438_);
v___y_405_ = v___y_433_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_434_;
v___y_409_ = v___y_438_;
v___y_410_ = v___y_436_;
v___y_411_ = v___y_437_;
v___y_412_ = v___y_438_;
goto v___jp_404_;
}
else
{
lean_object* v_val_440_; 
v_val_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v___x_439_, 1);
v___y_405_ = v___y_433_;
v___y_406_ = v___y_434_;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_434_;
v___y_409_ = v___y_438_;
v___y_410_ = v___y_436_;
v___y_411_ = v___y_437_;
v___y_412_ = v_val_440_;
goto v___jp_404_;
}
}
v___jp_441_:
{
lean_object* v_toCold_444_; lean_object* v_ref_445_; uint8_t v_suppressElabErrors_446_; lean_object* v___x_447_; lean_object* v___f_448_; lean_object* v_ref_449_; lean_object* v___x_450_; 
v_toCold_444_ = lean_ctor_get(v___y_364_, 0);
v_ref_445_ = lean_ctor_get(v___y_364_, 2);
v_suppressElabErrors_446_ = lean_ctor_get_uint8(v___y_364_, sizeof(void*)*3 + 2);
v___x_447_ = lean_box(v_suppressElabErrors_446_);
v___f_448_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_448_, 0, v___x_447_);
v_ref_449_ = l_Lean_replaceRef(v_ref_358_, v_ref_445_);
v___x_450_ = l_Lean_Syntax_getPos_x3f(v_ref_449_, v___y_442_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v___x_451_; 
v___x_451_ = lean_unsigned_to_nat(0u);
v___y_432_ = v_suppressElabErrors_446_;
v___y_433_ = v___f_448_;
v___y_434_ = v_toCold_444_;
v___y_435_ = v_ref_449_;
v___y_436_ = v___y_443_;
v___y_437_ = v___y_442_;
v___y_438_ = v___x_451_;
goto v___jp_431_;
}
else
{
lean_object* v_val_452_; 
v_val_452_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_val_452_);
lean_dec_ref_known(v___x_450_, 1);
v___y_432_ = v_suppressElabErrors_446_;
v___y_433_ = v___f_448_;
v___y_434_ = v_toCold_444_;
v___y_435_ = v_ref_449_;
v___y_436_ = v___y_443_;
v___y_437_ = v___y_442_;
v___y_438_ = v_val_452_;
goto v___jp_431_;
}
}
v___jp_454_:
{
uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_456_ = 1;
v___x_457_ = l_Lean_instBEqMessageSeverity_beq(v_severity_360_, v___x_456_);
if (v___x_457_ == 0)
{
v___y_442_ = v___y_455_;
v___y_443_ = v_severity_360_;
goto v___jp_441_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_364_);
v___x_459_ = l_Lean_warningAsError;
v___x_460_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v___x_458_, v___x_459_);
lean_dec_ref(v___x_458_);
if (v___x_460_ == 0)
{
v___y_442_ = v___y_455_;
v___y_443_ = v_severity_360_;
goto v___jp_441_;
}
else
{
v___y_442_ = v___y_455_;
v___y_443_ = v___x_453_;
goto v___jp_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___boxed(lean_object* v_ref_465_, lean_object* v_msgData_466_, lean_object* v_severity_467_, lean_object* v_isSilent_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
uint8_t v_severity_boxed_474_; uint8_t v_isSilent_boxed_475_; lean_object* v_res_476_; 
v_severity_boxed_474_ = lean_unbox(v_severity_467_);
v_isSilent_boxed_475_ = lean_unbox(v_isSilent_468_);
v_res_476_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_465_, v_msgData_466_, v_severity_boxed_474_, v_isSilent_boxed_475_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v_ref_465_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(lean_object* v_ref_477_, lean_object* v_msgData_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
uint8_t v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; 
v___x_488_ = 1;
v___x_489_ = 0;
v___x_490_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_477_, v_msgData_478_, v___x_488_, v___x_489_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3___boxed(lean_object* v_ref_491_, lean_object* v_msgData_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_ref_491_, v_msgData_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v_ref_491_);
return v_res_502_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__1));
v___x_507_ = l_Lean_MessageData_ofFormat(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2(lean_object* v___f_508_, lean_object* v_stx_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___y_520_; lean_object* v_wildcardHyps_x3f_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_559_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_516_);
v___x_560_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_561_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v___x_559_, v___x_560_);
lean_dec_ref(v___x_559_);
if (v___x_561_ == 0)
{
goto v___jp_533_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2, &l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2);
v___x_563_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_stx_509_, v___x_562_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_dec_ref_known(v___x_563_, 1);
goto v___jp_533_;
}
else
{
lean_dec_ref(v___f_508_);
return v___x_563_;
}
}
v___jp_519_:
{
lean_object* v___f_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___f_530_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed), 11, 1);
lean_closure_set(v___f_530_, 0, v_wildcardHyps_x3f_521_);
v___x_531_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_cbvTarget___boxed), 9, 0);
v___x_532_ = l_Lean_Elab_Tactic_withLocation(v___y_520_, v___f_530_, v___x_531_, v___f_508_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_520_);
return v___x_532_;
}
v___jp_533_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = l_Lean_Syntax_getArg(v_stx_509_, v___x_534_);
v___x_536_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_535_);
lean_dec(v___x_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_511_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_Lean_MVarId_getNondepPropHyps(v_a_538_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v_a_540_);
v___y_520_ = v___x_536_;
v_wildcardHyps_x3f_521_ = v___x_541_;
v___y_522_ = v___y_510_;
v___y_523_ = v___y_511_;
v___y_524_ = v___y_512_;
v___y_525_ = v___y_513_;
v___y_526_ = v___y_514_;
v___y_527_ = v___y_515_;
v___y_528_ = v___y_516_;
v___y_529_ = v___y_517_;
goto v___jp_519_;
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v___f_508_);
v_a_542_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_539_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_539_);
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
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec_ref(v___f_508_);
v_a_550_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_537_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_537_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_object* v___x_558_; 
v___x_558_ = lean_box(0);
v___y_520_ = v___x_536_;
v_wildcardHyps_x3f_521_ = v___x_558_;
v___y_522_ = v___y_510_;
v___y_523_ = v___y_511_;
v___y_524_ = v___y_512_;
v___y_525_ = v___y_513_;
v___y_526_ = v___y_514_;
v___y_527_ = v___y_515_;
v___y_528_ = v___y_516_;
v___y_529_ = v___y_517_;
goto v___jp_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___boxed(lean_object* v___f_564_, lean_object* v_stx_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2(v___f_564_, v_stx_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v_stx_565_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv(lean_object* v_stx_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___x_589_; 
v___f_587_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___closed__0));
v___f_588_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___boxed), 11, 2);
lean_closure_set(v___f_588_, 0, v___f_587_);
lean_closure_set(v___f_588_, 1, v_stx_577_);
v___x_589_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_588_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___boxed(lean_object* v_stx_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Elab_Tactic_Cbv_evalCbv(v_stx_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_);
lean_dec(v_a_598_);
lean_dec_ref(v_a_597_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(lean_object* v_00_u03b1_601_, lean_object* v_msg_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v_msg_602_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___boxed(lean_object* v_00_u03b1_613_, lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(v_00_u03b1_613_, v_msg_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5(lean_object* v_ref_625_, lean_object* v_msgData_626_, uint8_t v_severity_627_, uint8_t v_isSilent_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_625_, v_msgData_626_, v_severity_627_, v_isSilent_628_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___boxed(lean_object* v_ref_639_, lean_object* v_msgData_640_, lean_object* v_severity_641_, lean_object* v_isSilent_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
uint8_t v_severity_boxed_652_; uint8_t v_isSilent_boxed_653_; lean_object* v_res_654_; 
v_severity_boxed_652_ = lean_unbox(v_severity_641_);
v_isSilent_boxed_653_ = lean_unbox(v_isSilent_642_);
v_res_654_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5(v_ref_639_, v_msgData_640_, v_severity_boxed_652_, v_isSilent_boxed_653_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v_ref_639_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1(){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_672_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3));
v___x_674_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6));
v___x_675_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___boxed), 10, 0);
v___x_676_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_672_, v___x_673_, v___x_674_, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___boxed(lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
return v_res_678_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_box(0);
v___x_680_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0);
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___boxed(lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(lean_object* v_00_u03b1_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___boxed(lean_object* v_00_u03b1_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(v_00_u03b1_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(lean_object* v_msg_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_ref_715_; lean_object* v___x_716_; lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_725_; 
v_ref_715_ = lean_ctor_get(v___y_712_, 2);
v___x_716_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msg_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_725_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_725_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_723_; 
lean_inc(v_ref_715_);
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v_ref_715_);
lean_ctor_set(v___x_721_, 1, v_a_717_);
if (v_isShared_720_ == 0)
{
lean_ctor_set_tag(v___x_719_, 1);
lean_ctor_set(v___x_719_, 0, v___x_721_);
v___x_723_ = v___x_719_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___boxed(lean_object* v_msg_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v_msg_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
return v_res_732_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0));
v___x_735_ = l_Lean_stringToMessageData(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1, &l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1);
v___x_743_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v___x_742_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___boxed(lean_object* v_x_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(v_x_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v_x_744_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(uint8_t v___x_754_, lean_object* v___f_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___y_766_; lean_object* v___x_778_; 
v___x_778_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_757_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; uint8_t v___x_781_; uint8_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_780_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1));
v___x_781_ = 0;
v___x_782_ = 0;
v___x_783_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_783_, 0, v___x_781_);
lean_ctor_set_uint8(v___x_783_, 1, v___x_754_);
lean_ctor_set_uint8(v___x_783_, 2, v___x_782_);
lean_ctor_set_uint8(v___x_783_, 3, v___x_754_);
v___x_784_ = l_Lean_MVarId_applyConst(v_a_779_, v___x_780_, v___x_783_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
if (lean_obj_tag(v_a_785_) == 1)
{
lean_object* v_tail_786_; 
v_tail_786_ = lean_ctor_get(v_a_785_, 1);
if (lean_obj_tag(v_tail_786_) == 0)
{
lean_object* v_head_787_; lean_object* v___x_788_; 
lean_dec_ref(v___f_755_);
v_head_787_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_head_787_);
lean_dec_ref_known(v_a_785_, 2);
v___x_788_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_head_787_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v___y_766_ = v___x_788_;
goto v___jp_765_;
}
else
{
lean_object* v___x_789_; 
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
v___x_789_ = lean_apply_6(v___f_755_, v_a_785_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, lean_box(0));
v___y_766_ = v___x_789_;
goto v___jp_765_;
}
}
else
{
lean_object* v___x_790_; 
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
v___x_790_ = lean_apply_6(v___f_755_, v_a_785_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, lean_box(0));
v___y_766_ = v___x_790_;
goto v___jp_765_;
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec_ref(v___f_755_);
v_a_791_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_784_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_784_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec_ref(v___f_755_);
v_a_799_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_778_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_778_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
v___jp_765_:
{
if (lean_obj_tag(v___y_766_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec_ref_known(v___y_766_, 1);
v___x_767_ = lean_box(0);
v___x_768_ = lean_box(0);
v___x_769_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_767_, v___y_757_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v___x_769_, 0);
lean_dec(v_unused_777_);
v___x_771_ = v___x_769_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_dec(v___x_769_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_768_);
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_768_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
else
{
return v___x_769_;
}
}
else
{
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v___y_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed(lean_object* v___x_807_, lean_object* v___f_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
uint8_t v___x_1719__boxed_818_; lean_object* v_res_819_; 
v___x_1719__boxed_818_ = lean_unbox(v___x_807_);
v_res_819_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(v___x_1719__boxed_818_, v___f_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v_res_819_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1));
v___x_824_ = l_Lean_MessageData_ofFormat(v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(lean_object* v___f_825_, lean_object* v_stx_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_836_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_833_);
v___x_837_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_838_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v___x_836_, v___x_837_);
lean_dec_ref(v___x_836_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_825_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2, &l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2);
v___x_841_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_stx_826_, v___x_840_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_842_; 
lean_dec_ref_known(v___x_841_, 1);
v___x_842_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_825_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
return v___x_842_;
}
else
{
lean_dec_ref(v___f_825_);
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed(lean_object* v___f_843_, lean_object* v_stx_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(v___f_843_, v_stx_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v_stx_844_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv(lean_object* v_stx_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1));
lean_inc(v_stx_862_);
v___x_873_ = l_Lean_Syntax_isOfKind(v_stx_862_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec(v_stx_862_);
v___x_874_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v___x_874_;
}
else
{
lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___x_879_; 
v___f_875_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2));
v___x_876_ = lean_box(v___x_873_);
v___f_877_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed), 11, 2);
lean_closure_set(v___f_877_, 0, v___x_876_);
lean_closure_set(v___f_877_, 1, v___f_875_);
v___f_878_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed), 11, 2);
lean_closure_set(v___f_878_, 0, v___f_877_);
lean_closure_set(v___f_878_, 1, v_stx_862_);
v___x_879_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_878_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed(lean_object* v_stx_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv(v_stx_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(lean_object* v_00_u03b1_891_, lean_object* v_msg_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v_msg_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___boxed(lean_object* v_00_u03b1_899_, lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(v_00_u03b1_899_, v_msg_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1(){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_915_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_916_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1));
v___x_917_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1));
v___x_918_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed), 10, 0);
v___x_919_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_915_, v___x_916_, v___x_917_, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___boxed(lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
return v_res_921_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Cbv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
