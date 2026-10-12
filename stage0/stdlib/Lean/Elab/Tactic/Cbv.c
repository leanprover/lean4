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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0(lean_object* v_fvarId_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
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
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v_res_47_;
v_res_47_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0(v_fvarId_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
stack->m_obj
 = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0___boxed(lean_object* v_fvarId_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0(v_fvarId_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
return v_res_58_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(lean_object* v_fvarId_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___f_69_; lean_object* v___x_70_; 
v___f_69_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___lam__0___boxed), 10, 1);
lean_closure_set(v___f_69_, 0, v_fvarId_59_);
v___x_70_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_69_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
return v___x_70_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_cbvLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_59_ = stack[0].m_obj;
lean_object* v_a_60_ = stack[1].m_obj;
lean_object* v_a_61_ = stack[2].m_obj;
lean_object* v_a_62_ = stack[3].m_obj;
lean_object* v_a_63_ = stack[4].m_obj;
lean_object* v_a_64_ = stack[5].m_obj;
lean_object* v_a_65_ = stack[6].m_obj;
lean_object* v_a_66_ = stack[7].m_obj;
lean_object* v_a_67_ = stack[8].m_obj;
lean_object* v_res_71_;
v_res_71_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvLocalDecl___boxed(lean_object* v_fvarId_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
return v_res_82_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0(lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_a_93_; lean_object* v___x_104_; 
v___x_104_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_84_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_106_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v___x_106_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_a_105_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_106_, 1);
if (lean_obj_tag(v_a_107_) == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_box(0);
v_a_93_ = v___x_108_;
goto v___jp_92_;
}
else
{
lean_object* v_val_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_val_109_ = lean_ctor_get(v_a_107_, 0);
lean_inc(v_val_109_);
lean_dec_ref_known(v_a_107_, 1);
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v_val_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v_a_93_ = v___x_111_;
goto v___jp_92_;
}
}
else
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_119_; 
v_a_112_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_119_ == 0)
{
v___x_114_ = v___x_106_;
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_106_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_119_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_117_; 
if (v_isShared_115_ == 0)
{
v___x_117_ = v___x_114_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_a_112_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_104_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_104_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
v___jp_92_:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_box(0);
v___x_95_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_93_, v___y_84_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v___x_95_, 0);
lean_dec(v_unused_103_);
v___x_97_ = v___x_95_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_dec(v___x_95_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_94_);
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_94_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
else
{
return v___x_95_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_83_ = stack[0].m_obj;
lean_object* v___y_84_ = stack[1].m_obj;
lean_object* v___y_85_ = stack[2].m_obj;
lean_object* v___y_86_ = stack[3].m_obj;
lean_object* v___y_87_ = stack[4].m_obj;
lean_object* v___y_88_ = stack[5].m_obj;
lean_object* v___y_89_ = stack[6].m_obj;
lean_object* v___y_90_ = stack[7].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0(v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0___boxed(lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Elab_Tactic_Cbv_cbvTarget___lam__0(v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_138_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget(lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___f_149_; lean_object* v___x_150_; 
v___f_149_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_cbvTarget___closed__0));
v___x_150_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_149_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
return v___x_150_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_cbvTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_140_ = stack[0].m_obj;
lean_object* v_a_141_ = stack[1].m_obj;
lean_object* v_a_142_ = stack[2].m_obj;
lean_object* v_a_143_ = stack[3].m_obj;
lean_object* v_a_144_ = stack[4].m_obj;
lean_object* v_a_145_ = stack[5].m_obj;
lean_object* v_a_146_ = stack[6].m_obj;
lean_object* v_a_147_ = stack[7].m_obj;
lean_object* v_res_151_;
v_res_151_ = l_Lean_Elab_Tactic_Cbv_cbvTarget(v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
stack->m_obj
 = v_res_151_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_cbvTarget___boxed(lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Elab_Tactic_Cbv_cbvTarget(v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
return v_res_161_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(lean_object* v_opts_162_, lean_object* v_opt_163_){
_start:
{
lean_object* v_name_164_; lean_object* v_defValue_165_; lean_object* v_map_166_; lean_object* v___x_167_; 
v_name_164_ = lean_ctor_get(v_opt_163_, 0);
v_defValue_165_ = lean_ctor_get(v_opt_163_, 1);
v_map_166_ = lean_ctor_get(v_opts_162_, 0);
v___x_167_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_166_, v_name_164_);
if (lean_obj_tag(v___x_167_) == 0)
{
uint8_t v___x_168_; 
v___x_168_ = lean_unbox(v_defValue_165_);
return v___x_168_;
}
else
{
lean_object* v_val_169_; 
v_val_169_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v___x_167_, 1);
if (lean_obj_tag(v_val_169_) == 1)
{
uint8_t v_v_170_; 
v_v_170_ = lean_ctor_get_uint8(v_val_169_, 0);
lean_dec_ref_known(v_val_169_, 0);
return v_v_170_;
}
else
{
uint8_t v___x_171_; 
lean_dec(v_val_169_);
v___x_171_ = lean_unbox(v_defValue_165_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_162_ = stack[0].m_obj;
lean_object* v_opt_163_ = stack[1].m_obj;
uint8_t v_res_172_;
v_res_172_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v_opts_162_, v_opt_163_);
stack->m_num = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2___boxed(lean_object* v_opts_173_, lean_object* v_opt_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v_opts_173_, v_opt_174_);
lean_dec_ref(v_opt_174_);
lean_dec_ref(v_opts_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(lean_object* v_msgData_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; lean_object* v_env_184_; uint8_t v___x_185_; lean_object* v_env_186_; lean_object* v___x_187_; lean_object* v_toCold_188_; lean_object* v_mctx_189_; lean_object* v_lctx_190_; lean_object* v_options_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_183_ = lean_st_ref_get(v___y_181_);
v_env_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc_ref(v_env_184_);
lean_dec(v___x_183_);
v___x_185_ = 0;
v_env_186_ = l_Lean_Environment_setRecordingDeps(v_env_184_, v___x_185_);
v___x_187_ = lean_st_ref_get(v___y_179_);
v_toCold_188_ = lean_ctor_get(v___y_180_, 0);
v_mctx_189_ = lean_ctor_get(v___x_187_, 0);
lean_inc_ref(v_mctx_189_);
lean_dec(v___x_187_);
v_lctx_190_ = lean_ctor_get(v___y_178_, 2);
v_options_191_ = lean_ctor_get(v_toCold_188_, 2);
lean_inc_ref(v_options_191_);
lean_inc_ref(v_lctx_190_);
v___x_192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_192_, 0, v_env_186_);
lean_ctor_set(v___x_192_, 1, v_mctx_189_);
lean_ctor_set(v___x_192_, 2, v_lctx_190_);
lean_ctor_set(v___x_192_, 3, v_options_191_);
v___x_193_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_msgData_177_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_177_ = stack[0].m_obj;
lean_object* v___y_178_ = stack[1].m_obj;
lean_object* v___y_179_ = stack[2].m_obj;
lean_object* v___y_180_ = stack[3].m_obj;
lean_object* v___y_181_ = stack[4].m_obj;
lean_object* v_res_195_;
v_res_195_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msgData_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0___boxed(lean_object* v_msgData_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msgData_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
return v_res_202_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(lean_object* v_msg_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_ref_209_; lean_object* v___x_210_; lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_219_; 
v_ref_209_ = lean_ctor_get(v___y_206_, 2);
v___x_210_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msg_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_219_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
lean_inc(v_ref_209_);
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v_ref_209_);
lean_ctor_set(v___x_215_, 1, v_a_211_);
if (v_isShared_214_ == 0)
{
lean_ctor_set_tag(v___x_213_, 1);
lean_ctor_set(v___x_213_, 0, v___x_215_);
v___x_217_ = v___x_213_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_203_ = stack[0].m_obj;
lean_object* v___y_204_ = stack[1].m_obj;
lean_object* v___y_205_ = stack[2].m_obj;
lean_object* v___y_206_ = stack[3].m_obj;
lean_object* v___y_207_ = stack[4].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v_msg_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg___boxed(lean_object* v_msg_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v_msg_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
return v_res_227_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__0));
v___x_230_ = l_Lean_stringToMessageData(v___x_229_);
return v___x_230_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(lean_object* v_x_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1, &l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___closed__1);
v___x_242_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v___x_241_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
return v___x_242_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_231_ = stack[0].m_obj;
lean_object* v___y_232_ = stack[1].m_obj;
lean_object* v___y_233_ = stack[2].m_obj;
lean_object* v___y_234_ = stack[3].m_obj;
lean_object* v___y_235_ = stack[4].m_obj;
lean_object* v___y_236_ = stack[5].m_obj;
lean_object* v___y_237_ = stack[6].m_obj;
lean_object* v___y_238_ = stack[7].m_obj;
lean_object* v___y_239_ = stack[8].m_obj;
lean_object* v_res_243_;
v_res_243_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(v_x_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0___boxed(lean_object* v_x_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__0(v_x_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v_x_244_);
return v_res_254_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(lean_object* v_a_255_, lean_object* v_as_256_, size_t v_i_257_, size_t v_stop_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = lean_usize_dec_eq(v_i_257_, v_stop_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_array_uget_borrowed(v_as_256_, v_i_257_);
v___x_261_ = l_Lean_instBEqFVarId_beq(v_a_255_, v___x_260_);
if (v___x_261_ == 0)
{
size_t v___x_262_; size_t v___x_263_; 
v___x_262_ = ((size_t)1ULL);
v___x_263_ = lean_usize_add(v_i_257_, v___x_262_);
v_i_257_ = v___x_263_;
goto _start;
}
else
{
return v___x_261_;
}
}
else
{
uint8_t v___x_265_; 
v___x_265_ = 0;
return v___x_265_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_255_ = stack[0].m_obj;
lean_object* v_as_256_ = stack[1].m_obj;
size_t v_i_257_ = stack[2].m_num;
size_t v_stop_258_ = stack[3].m_num;
uint8_t v_res_266_;
v_res_266_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(v_a_255_, v_as_256_, v_i_257_, v_stop_258_);
stack->m_num = v_res_266_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2___boxed(lean_object* v_a_267_, lean_object* v_as_268_, lean_object* v_i_269_, lean_object* v_stop_270_){
_start:
{
size_t v_i_boxed_271_; size_t v_stop_boxed_272_; uint8_t v_res_273_; lean_object* v_r_274_; 
v_i_boxed_271_ = lean_unbox_usize(v_i_269_);
lean_dec(v_i_269_);
v_stop_boxed_272_ = lean_unbox_usize(v_stop_270_);
lean_dec(v_stop_270_);
v_res_273_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(v_a_267_, v_as_268_, v_i_boxed_271_, v_stop_boxed_272_);
lean_dec_ref(v_as_268_);
lean_dec(v_a_267_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
uint8_t l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(lean_object* v_as_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_array_get_size(v_as_275_);
v___x_279_ = lean_nat_dec_lt(v___x_277_, v___x_278_);
if (v___x_279_ == 0)
{
return v___x_279_;
}
else
{
if (v___x_279_ == 0)
{
return v___x_279_;
}
else
{
size_t v___x_280_; size_t v___x_281_; uint8_t v___x_282_; 
v___x_280_ = ((size_t)0ULL);
v___x_281_ = lean_usize_of_nat(v___x_278_);
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_spec__2(v_a_276_, v_as_275_, v___x_280_, v___x_281_);
return v___x_282_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_275_ = stack[0].m_obj;
lean_object* v_a_276_ = stack[1].m_obj;
uint8_t v_res_283_;
v_res_283_ = l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_as_275_, v_a_276_);
stack->m_num = v_res_283_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1___boxed(lean_object* v_as_284_, lean_object* v_a_285_){
_start:
{
uint8_t v_res_286_; lean_object* v_r_287_; 
v_res_286_ = l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_as_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_as_284_);
v_r_287_ = lean_box(v_res_286_);
return v_r_287_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(lean_object* v_wildcardHyps_x3f_288_, lean_object* v_fvarId_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
if (lean_obj_tag(v_wildcardHyps_x3f_288_) == 1)
{
lean_object* v_val_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_309_; 
v_val_299_ = lean_ctor_get(v_wildcardHyps_x3f_288_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_wildcardHyps_x3f_288_);
if (v_isSharedCheck_309_ == 0)
{
v___x_301_ = v_wildcardHyps_x3f_288_;
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_val_299_);
lean_dec(v_wildcardHyps_x3f_288_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
uint8_t v___x_303_; 
v___x_303_ = l_Array_contains___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__1(v_val_299_, v_fvarId_289_);
lean_dec(v_val_299_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_306_; 
lean_dec(v_fvarId_289_);
v___x_304_ = lean_box(0);
if (v_isShared_302_ == 0)
{
lean_ctor_set_tag(v___x_301_, 0);
lean_ctor_set(v___x_301_, 0, v___x_304_);
v___x_306_ = v___x_301_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
else
{
lean_object* v___x_308_; 
lean_del_object(v___x_301_);
v___x_308_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
return v___x_308_;
}
}
}
else
{
lean_object* v___x_310_; 
lean_dec(v_wildcardHyps_x3f_288_);
v___x_310_ = l_Lean_Elab_Tactic_Cbv_cbvLocalDecl(v_fvarId_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
return v___x_310_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_wildcardHyps_x3f_288_ = stack[0].m_obj;
lean_object* v_fvarId_289_ = stack[1].m_obj;
lean_object* v___y_290_ = stack[2].m_obj;
lean_object* v___y_291_ = stack[3].m_obj;
lean_object* v___y_292_ = stack[4].m_obj;
lean_object* v___y_293_ = stack[5].m_obj;
lean_object* v___y_294_ = stack[6].m_obj;
lean_object* v___y_295_ = stack[7].m_obj;
lean_object* v___y_296_ = stack[8].m_obj;
lean_object* v___y_297_ = stack[9].m_obj;
lean_object* v_res_311_;
v_res_311_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(v_wildcardHyps_x3f_288_, v_fvarId_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed(lean_object* v_wildcardHyps_x3f_312_, lean_object* v_fvarId_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1(v_wildcardHyps_x3f_312_, v_fvarId_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_323_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(uint8_t v_suppressElabErrors_332_, uint8_t v___y_333_, lean_object* v_x_334_){
_start:
{
if (lean_obj_tag(v_x_334_) == 1)
{
lean_object* v_pre_335_; 
v_pre_335_ = lean_ctor_get(v_x_334_, 0);
switch(lean_obj_tag(v_pre_335_))
{
case 1:
{
lean_object* v_pre_336_; 
v_pre_336_ = lean_ctor_get(v_pre_335_, 0);
switch(lean_obj_tag(v_pre_336_))
{
case 0:
{
lean_object* v_str_337_; lean_object* v_str_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v_str_337_ = lean_ctor_get(v_x_334_, 1);
v_str_338_ = lean_ctor_get(v_pre_335_, 1);
v___x_339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__0));
v___x_340_ = lean_string_dec_eq(v_str_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__1));
v___x_342_ = lean_string_dec_eq(v_str_338_, v___x_341_);
if (v___x_342_ == 0)
{
return v___x_342_;
}
else
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__2));
v___x_344_ = lean_string_dec_eq(v_str_337_, v___x_343_);
if (v___x_344_ == 0)
{
return v___x_344_;
}
else
{
return v_suppressElabErrors_332_;
}
}
}
else
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__3));
v___x_346_ = lean_string_dec_eq(v_str_337_, v___x_345_);
if (v___x_346_ == 0)
{
return v___x_346_;
}
else
{
return v_suppressElabErrors_332_;
}
}
}
case 1:
{
lean_object* v_pre_347_; 
v_pre_347_ = lean_ctor_get(v_pre_336_, 0);
if (lean_obj_tag(v_pre_347_) == 0)
{
lean_object* v_str_348_; lean_object* v_str_349_; lean_object* v_str_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_str_348_ = lean_ctor_get(v_x_334_, 1);
v_str_349_ = lean_ctor_get(v_pre_335_, 1);
v_str_350_ = lean_ctor_get(v_pre_336_, 1);
v___x_351_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__4));
v___x_352_ = lean_string_dec_eq(v_str_350_, v___x_351_);
if (v___x_352_ == 0)
{
return v___x_352_;
}
else
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__5));
v___x_354_ = lean_string_dec_eq(v_str_349_, v___x_353_);
if (v___x_354_ == 0)
{
return v___x_354_;
}
else
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__6));
v___x_356_ = lean_string_dec_eq(v_str_348_, v___x_355_);
if (v___x_356_ == 0)
{
return v___x_356_;
}
else
{
return v_suppressElabErrors_332_;
}
}
}
}
else
{
return v___y_333_;
}
}
default: 
{
return v___y_333_;
}
}
}
case 0:
{
lean_object* v_str_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_str_357_ = lean_ctor_get(v_x_334_, 1);
v___x_358_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___closed__7));
v___x_359_ = lean_string_dec_eq(v_str_357_, v___x_358_);
if (v___x_359_ == 0)
{
return v___x_359_;
}
else
{
return v_suppressElabErrors_332_;
}
}
default: 
{
return v___y_333_;
}
}
}
else
{
return v___y_333_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_332_ = stack[0].m_num;
uint8_t v___y_333_ = stack[1].m_num;
lean_object* v_x_334_ = stack[2].m_obj;
uint8_t v_res_360_;
v_res_360_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(v_suppressElabErrors_332_, v___y_333_, v_x_334_);
stack->m_num = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_361_, lean_object* v___y_362_, lean_object* v_x_363_){
_start:
{
uint8_t v_suppressElabErrors_boxed_364_; uint8_t v___y_7738__boxed_365_; uint8_t v_res_366_; lean_object* v_r_367_; 
v_suppressElabErrors_boxed_364_ = lean_unbox(v_suppressElabErrors_361_);
v___y_7738__boxed_365_ = lean_unbox(v___y_362_);
v_res_366_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0(v_suppressElabErrors_boxed_364_, v___y_7738__boxed_365_, v_x_363_);
lean_dec(v_x_363_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(lean_object* v_ref_369_, lean_object* v_msgData_370_, uint8_t v_severity_371_, uint8_t v_isSilent_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; uint8_t v___y_384_; uint8_t v___y_385_; lean_object* v_toCold_386_; lean_object* v___y_387_; lean_object* v___y_416_; lean_object* v___y_417_; uint8_t v___y_418_; lean_object* v___y_419_; uint8_t v___y_420_; uint8_t v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_443_; uint8_t v___y_444_; lean_object* v___y_445_; uint8_t v___y_446_; lean_object* v___y_447_; uint8_t v___y_448_; lean_object* v___y_449_; uint8_t v___y_453_; uint8_t v___y_454_; uint8_t v___y_455_; uint8_t v___x_466_; uint8_t v___y_468_; uint8_t v___y_469_; uint8_t v___y_470_; uint8_t v___y_472_; uint8_t v___x_480_; 
v___x_466_ = 2;
v___x_480_ = l_Lean_instBEqMessageSeverity_beq(v_severity_371_, v___x_466_);
if (v___x_480_ == 0)
{
v___y_472_ = v___x_480_;
goto v___jp_471_;
}
else
{
uint8_t v___x_481_; 
lean_inc_ref(v_msgData_370_);
v___x_481_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_370_);
v___y_472_ = v___x_481_;
goto v___jp_471_;
}
v___jp_378_:
{
lean_object* v_currNamespace_388_; lean_object* v_openDecls_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_env_394_; lean_object* v_nextMacroScope_395_; lean_object* v_ngen_396_; lean_object* v_auxDeclNGen_397_; lean_object* v_traceState_398_; lean_object* v_cache_399_; lean_object* v_recordedDeps_400_; lean_object* v_messages_401_; lean_object* v_infoState_402_; lean_object* v_snapshotTasks_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_414_; 
v_currNamespace_388_ = lean_ctor_get(v_toCold_386_, 4);
v_openDecls_389_ = lean_ctor_get(v_toCold_386_, 5);
lean_inc(v_openDecls_389_);
lean_inc(v_currNamespace_388_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_currNamespace_388_);
lean_ctor_set(v___x_390_, 1, v_openDecls_389_);
v___x_391_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___y_383_);
lean_inc_ref(v___y_380_);
lean_inc_ref(v___y_379_);
v___x_392_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_392_, 0, v___y_379_);
lean_ctor_set(v___x_392_, 1, v___y_382_);
lean_ctor_set(v___x_392_, 2, v___y_381_);
lean_ctor_set(v___x_392_, 3, v___y_380_);
lean_ctor_set(v___x_392_, 4, v___x_391_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*5, v___y_384_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*5 + 1, v___y_385_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*5 + 2, v_isSilent_372_);
v___x_393_ = lean_st_ref_take(v___y_387_);
v_env_394_ = lean_ctor_get(v___x_393_, 0);
v_nextMacroScope_395_ = lean_ctor_get(v___x_393_, 1);
v_ngen_396_ = lean_ctor_get(v___x_393_, 2);
v_auxDeclNGen_397_ = lean_ctor_get(v___x_393_, 3);
v_traceState_398_ = lean_ctor_get(v___x_393_, 4);
v_cache_399_ = lean_ctor_get(v___x_393_, 5);
v_recordedDeps_400_ = lean_ctor_get(v___x_393_, 6);
v_messages_401_ = lean_ctor_get(v___x_393_, 7);
v_infoState_402_ = lean_ctor_get(v___x_393_, 8);
v_snapshotTasks_403_ = lean_ctor_get(v___x_393_, 9);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_414_ == 0)
{
v___x_405_ = v___x_393_;
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_snapshotTasks_403_);
lean_inc(v_infoState_402_);
lean_inc(v_messages_401_);
lean_inc(v_recordedDeps_400_);
lean_inc(v_cache_399_);
lean_inc(v_traceState_398_);
lean_inc(v_auxDeclNGen_397_);
lean_inc(v_ngen_396_);
lean_inc(v_nextMacroScope_395_);
lean_inc(v_env_394_);
lean_dec(v___x_393_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_414_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_407_ = lean_box(0);
v___x_408_ = l_Lean_MessageLog_add(v___x_392_, v_messages_401_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 7, v___x_408_);
v___x_410_ = v___x_405_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_env_394_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_nextMacroScope_395_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_ngen_396_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_auxDeclNGen_397_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_traceState_398_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v_cache_399_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_recordedDeps_400_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_infoState_402_);
lean_ctor_set(v_reuseFailAlloc_413_, 9, v_snapshotTasks_403_);
v___x_410_ = v_reuseFailAlloc_413_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_st_ref_put(v___y_387_, v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_407_);
return v___x_412_;
}
}
}
v___jp_415_:
{
lean_object* v_fileName_424_; lean_object* v_fileMap_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_441_; 
v_fileName_424_ = lean_ctor_get(v___y_422_, 0);
v_fileMap_425_ = lean_ctor_get(v___y_422_, 1);
v___x_426_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_370_);
v___x_427_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v___x_426_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_441_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_441_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_441_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_inc_ref_n(v_fileMap_425_, 2);
v___x_432_ = l_Lean_FileMap_toPosition(v_fileMap_425_, v___y_419_);
lean_dec(v___y_419_);
v___x_433_ = l_Lean_FileMap_toPosition(v_fileMap_425_, v___y_423_);
lean_dec(v___y_423_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
v___x_435_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___closed__0));
if (v___y_418_ == 0)
{
lean_del_object(v___x_430_);
lean_dec_ref(v___y_416_);
v___y_379_ = v_fileName_424_;
v___y_380_ = v___x_435_;
v___y_381_ = v___x_434_;
v___y_382_ = v___x_432_;
v___y_383_ = v_a_428_;
v___y_384_ = v___y_420_;
v___y_385_ = v___y_421_;
v_toCold_386_ = v___y_417_;
v___y_387_ = v___y_376_;
goto v___jp_378_;
}
else
{
uint8_t v___x_436_; 
lean_inc(v_a_428_);
v___x_436_ = l_Lean_MessageData_hasTag(v___y_416_, v_a_428_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_439_; 
lean_dec_ref_known(v___x_434_, 1);
lean_dec_ref(v___x_432_);
lean_dec(v_a_428_);
v___x_437_ = lean_box(0);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_437_);
v___x_439_ = v___x_430_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
else
{
lean_del_object(v___x_430_);
v___y_379_ = v_fileName_424_;
v___y_380_ = v___x_435_;
v___y_381_ = v___x_434_;
v___y_382_ = v___x_432_;
v___y_383_ = v_a_428_;
v___y_384_ = v___y_420_;
v___y_385_ = v___y_421_;
v_toCold_386_ = v___y_417_;
v___y_387_ = v___y_376_;
goto v___jp_378_;
}
}
}
}
v___jp_442_:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Syntax_getTailPos_x3f(v___y_447_, v___y_446_);
lean_dec(v___y_447_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_inc(v___y_449_);
v___y_416_ = v___y_443_;
v___y_417_ = v___y_445_;
v___y_418_ = v___y_444_;
v___y_419_ = v___y_449_;
v___y_420_ = v___y_446_;
v___y_421_ = v___y_448_;
v___y_422_ = v___y_445_;
v___y_423_ = v___y_449_;
goto v___jp_415_;
}
else
{
lean_object* v_val_451_; 
v_val_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v___x_450_, 1);
v___y_416_ = v___y_443_;
v___y_417_ = v___y_445_;
v___y_418_ = v___y_444_;
v___y_419_ = v___y_449_;
v___y_420_ = v___y_446_;
v___y_421_ = v___y_448_;
v___y_422_ = v___y_445_;
v___y_423_ = v_val_451_;
goto v___jp_415_;
}
}
v___jp_452_:
{
lean_object* v_toCold_456_; lean_object* v_ref_457_; uint8_t v_suppressElabErrors_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___f_461_; lean_object* v_ref_462_; lean_object* v___x_463_; 
v_toCold_456_ = lean_ctor_get(v___y_375_, 0);
v_ref_457_ = lean_ctor_get(v___y_375_, 2);
v_suppressElabErrors_458_ = lean_ctor_get_uint8(v___y_375_, sizeof(void*)*3 + 2);
v___x_459_ = lean_box(v_suppressElabErrors_458_);
v___x_460_ = lean_box(v___y_453_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_461_, 0, v___x_459_);
lean_closure_set(v___f_461_, 1, v___x_460_);
v_ref_462_ = l_Lean_replaceRef(v_ref_369_, v_ref_457_);
v___x_463_ = l_Lean_Syntax_getPos_x3f(v_ref_462_, v___y_454_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_unsigned_to_nat(0u);
v___y_443_ = v___f_461_;
v___y_444_ = v_suppressElabErrors_458_;
v___y_445_ = v_toCold_456_;
v___y_446_ = v___y_454_;
v___y_447_ = v_ref_462_;
v___y_448_ = v___y_455_;
v___y_449_ = v___x_464_;
goto v___jp_442_;
}
else
{
lean_object* v_val_465_; 
v_val_465_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v___x_463_, 1);
v___y_443_ = v___f_461_;
v___y_444_ = v_suppressElabErrors_458_;
v___y_445_ = v_toCold_456_;
v___y_446_ = v___y_454_;
v___y_447_ = v_ref_462_;
v___y_448_ = v___y_455_;
v___y_449_ = v_val_465_;
goto v___jp_442_;
}
}
v___jp_467_:
{
if (v___y_470_ == 0)
{
v___y_453_ = v___y_468_;
v___y_454_ = v___y_469_;
v___y_455_ = v_severity_371_;
goto v___jp_452_;
}
else
{
v___y_453_ = v___y_468_;
v___y_454_ = v___y_469_;
v___y_455_ = v___x_466_;
goto v___jp_452_;
}
}
v___jp_471_:
{
if (v___y_472_ == 0)
{
uint8_t v___x_473_; uint8_t v___x_474_; 
v___x_473_ = 1;
v___x_474_ = l_Lean_instBEqMessageSeverity_beq(v_severity_371_, v___x_473_);
if (v___x_474_ == 0)
{
v___y_468_ = v___y_472_;
v___y_469_ = v___y_472_;
v___y_470_ = v___x_474_;
goto v___jp_467_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_475_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_375_);
v___x_476_ = l_Lean_warningAsError;
v___x_477_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v___x_475_, v___x_476_);
lean_dec_ref(v___x_475_);
v___y_468_ = v___y_472_;
v___y_469_ = v___y_472_;
v___y_470_ = v___x_477_;
goto v___jp_467_;
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v_msgData_370_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_369_ = stack[0].m_obj;
lean_object* v_msgData_370_ = stack[1].m_obj;
uint8_t v_severity_371_ = stack[2].m_num;
uint8_t v_isSilent_372_ = stack[3].m_num;
lean_object* v___y_373_ = stack[4].m_obj;
lean_object* v___y_374_ = stack[5].m_obj;
lean_object* v___y_375_ = stack[6].m_obj;
lean_object* v___y_376_ = stack[7].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_369_, v_msgData_370_, v_severity_371_, v_isSilent_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg___boxed(lean_object* v_ref_483_, lean_object* v_msgData_484_, lean_object* v_severity_485_, lean_object* v_isSilent_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
uint8_t v_severity_boxed_492_; uint8_t v_isSilent_boxed_493_; lean_object* v_res_494_; 
v_severity_boxed_492_ = lean_unbox(v_severity_485_);
v_isSilent_boxed_493_ = lean_unbox(v_isSilent_486_);
v_res_494_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_483_, v_msgData_484_, v_severity_boxed_492_, v_isSilent_boxed_493_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v_ref_483_);
return v_res_494_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(lean_object* v_ref_495_, lean_object* v_msgData_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
uint8_t v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; 
v___x_506_ = 1;
v___x_507_ = 0;
v___x_508_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_495_, v_msgData_496_, v___x_506_, v___x_507_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_508_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_495_ = stack[0].m_obj;
lean_object* v_msgData_496_ = stack[1].m_obj;
lean_object* v___y_497_ = stack[2].m_obj;
lean_object* v___y_498_ = stack[3].m_obj;
lean_object* v___y_499_ = stack[4].m_obj;
lean_object* v___y_500_ = stack[5].m_obj;
lean_object* v___y_501_ = stack[6].m_obj;
lean_object* v___y_502_ = stack[7].m_obj;
lean_object* v___y_503_ = stack[8].m_obj;
lean_object* v___y_504_ = stack[9].m_obj;
lean_object* v_res_509_;
v_res_509_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_ref_495_, v_msgData_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3___boxed(lean_object* v_ref_510_, lean_object* v_msgData_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_ref_510_, v_msgData_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v_ref_510_);
return v_res_521_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__1));
v___x_526_ = l_Lean_MessageData_ofFormat(v___x_525_);
return v___x_526_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2(lean_object* v___f_527_, lean_object* v_stx_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___y_539_; lean_object* v_wildcardHyps_x3f_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_578_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_535_);
v___x_579_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_580_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v___x_578_, v___x_579_);
lean_dec_ref(v___x_578_);
if (v___x_580_ == 0)
{
goto v___jp_552_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2, &l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___closed__2);
v___x_582_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_stx_528_, v___x_581_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_dec_ref_known(v___x_582_, 1);
goto v___jp_552_;
}
else
{
lean_dec_ref(v___f_527_);
return v___x_582_;
}
}
v___jp_538_:
{
lean_object* v___f_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___f_549_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__1___boxed), 11, 1);
lean_closure_set(v___f_549_, 0, v_wildcardHyps_x3f_540_);
v___x_550_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_cbvTarget___boxed), 9, 0);
v___x_551_ = l_Lean_Elab_Tactic_withLocation(v___y_539_, v___f_549_, v___x_550_, v___f_527_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_539_);
return v___x_551_;
}
v___jp_552_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = l_Lean_Syntax_getArg(v_stx_528_, v___x_553_);
v___x_555_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_554_);
lean_dec(v___x_554_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_530_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
v___x_558_ = l_Lean_MVarId_getNondepPropHyps(v_a_557_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_a_559_);
v___y_539_ = v___x_555_;
v_wildcardHyps_x3f_540_ = v___x_560_;
v___y_541_ = v___y_529_;
v___y_542_ = v___y_530_;
v___y_543_ = v___y_531_;
v___y_544_ = v___y_532_;
v___y_545_ = v___y_533_;
v___y_546_ = v___y_534_;
v___y_547_ = v___y_535_;
v___y_548_ = v___y_536_;
goto v___jp_538_;
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec_ref(v___f_527_);
v_a_561_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_558_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_558_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec_ref(v___f_527_);
v_a_569_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_556_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_556_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_box(0);
v___y_539_ = v___x_555_;
v_wildcardHyps_x3f_540_ = v___x_577_;
v___y_541_ = v___y_529_;
v___y_542_ = v___y_530_;
v___y_543_ = v___y_531_;
v___y_544_ = v___y_532_;
v___y_545_ = v___y_533_;
v___y_546_ = v___y_534_;
v___y_547_ = v___y_535_;
v___y_548_ = v___y_536_;
goto v___jp_538_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_527_ = stack[0].m_obj;
lean_object* v_stx_528_ = stack[1].m_obj;
lean_object* v___y_529_ = stack[2].m_obj;
lean_object* v___y_530_ = stack[3].m_obj;
lean_object* v___y_531_ = stack[4].m_obj;
lean_object* v___y_532_ = stack[5].m_obj;
lean_object* v___y_533_ = stack[6].m_obj;
lean_object* v___y_534_ = stack[7].m_obj;
lean_object* v___y_535_ = stack[8].m_obj;
lean_object* v___y_536_ = stack[9].m_obj;
lean_object* v_res_583_;
v_res_583_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2(v___f_527_, v_stx_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
stack->m_obj
 = v_res_583_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___boxed(lean_object* v___f_584_, lean_object* v_stx_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2(v___f_584_, v_stx_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v_stx_585_);
return v_res_595_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv(lean_object* v_stx_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___x_609_; 
v___f_607_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalCbv___closed__0));
v___f_608_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___lam__2___boxed), 11, 2);
lean_closure_set(v___f_608_, 0, v___f_607_);
lean_closure_set(v___f_608_, 1, v_stx_597_);
v___x_609_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_608_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
return v___x_609_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_evalCbv_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_597_ = stack[0].m_obj;
lean_object* v_a_598_ = stack[1].m_obj;
lean_object* v_a_599_ = stack[2].m_obj;
lean_object* v_a_600_ = stack[3].m_obj;
lean_object* v_a_601_ = stack[4].m_obj;
lean_object* v_a_602_ = stack[5].m_obj;
lean_object* v_a_603_ = stack[6].m_obj;
lean_object* v_a_604_ = stack[7].m_obj;
lean_object* v_a_605_ = stack[8].m_obj;
lean_object* v_res_610_;
v_res_610_ = l_Lean_Elab_Tactic_Cbv_evalCbv(v_stx_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalCbv___boxed(lean_object* v_stx_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Elab_Tactic_Cbv_evalCbv(v_stx_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec_ref(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
return v_res_621_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(lean_object* v_00_u03b1_622_, lean_object* v_msg_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___redArg(v_msg_623_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
return v___x_633_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_623_ = stack[1].m_obj;
lean_object* v___y_624_ = stack[2].m_obj;
lean_object* v___y_625_ = stack[3].m_obj;
lean_object* v___y_626_ = stack[4].m_obj;
lean_object* v___y_627_ = stack[5].m_obj;
lean_object* v___y_628_ = stack[6].m_obj;
lean_object* v___y_629_ = stack[7].m_obj;
lean_object* v___y_630_ = stack[8].m_obj;
lean_object* v___y_631_ = stack[9].m_obj;
lean_object* v_res_634_;
v_res_634_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(lean_box(0), v_msg_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0___boxed(lean_object* v_00_u03b1_635_, lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0(v_00_u03b1_635_, v_msg_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_646_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5(lean_object* v_ref_647_, lean_object* v_msgData_648_, uint8_t v_severity_649_, uint8_t v_isSilent_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___redArg(v_ref_647_, v_msgData_648_, v_severity_649_, v_isSilent_650_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v___x_660_;
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_647_ = stack[0].m_obj;
lean_object* v_msgData_648_ = stack[1].m_obj;
uint8_t v_severity_649_ = stack[2].m_num;
uint8_t v_isSilent_650_ = stack[3].m_num;
lean_object* v___y_651_ = stack[4].m_obj;
lean_object* v___y_652_ = stack[5].m_obj;
lean_object* v___y_653_ = stack[6].m_obj;
lean_object* v___y_654_ = stack[7].m_obj;
lean_object* v___y_655_ = stack[8].m_obj;
lean_object* v___y_656_ = stack[9].m_obj;
lean_object* v___y_657_ = stack[10].m_obj;
lean_object* v___y_658_ = stack[11].m_obj;
lean_object* v_res_661_;
v_res_661_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5(v_ref_647_, v_msgData_648_, v_severity_649_, v_isSilent_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
stack->m_obj
 = v_res_661_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5___boxed(lean_object* v_ref_662_, lean_object* v_msgData_663_, lean_object* v_severity_664_, lean_object* v_isSilent_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
uint8_t v_severity_boxed_675_; uint8_t v_isSilent_boxed_676_; lean_object* v_res_677_; 
v_severity_boxed_675_ = lean_unbox(v_severity_664_);
v_isSilent_boxed_676_ = lean_unbox(v_isSilent_665_);
v_res_677_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3_spec__5(v_ref_662_, v_msgData_663_, v_severity_boxed_675_, v_isSilent_boxed_676_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v_ref_662_);
return v_res_677_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1(){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_695_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_696_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__3));
v___x_697_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___closed__6));
v___x_698_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalCbv___boxed), 10, 0);
v___x_699_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_695_, v___x_696_, v___x_697_, v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_700_;
v_res_700_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
stack->m_obj
 = v_res_700_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1___boxed(lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalCbv__1();
return v_res_702_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = lean_box(0);
v___x_704_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___x_703_);
return v___x_705_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg(){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___closed__0);
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_709_;
v_res_709_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg___boxed(lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v_res_711_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(lean_object* v_00_u03b1_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v___x_722_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_713_ = stack[1].m_obj;
lean_object* v___y_714_ = stack[2].m_obj;
lean_object* v___y_715_ = stack[3].m_obj;
lean_object* v___y_716_ = stack[4].m_obj;
lean_object* v___y_717_ = stack[5].m_obj;
lean_object* v___y_718_ = stack[6].m_obj;
lean_object* v___y_719_ = stack[7].m_obj;
lean_object* v___y_720_ = stack[8].m_obj;
lean_object* v_res_723_;
v_res_723_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(lean_box(0), v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___boxed(lean_object* v_00_u03b1_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1(v_00_u03b1_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
return v_res_734_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(lean_object* v_msg_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_ref_741_; lean_object* v___x_742_; lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_751_; 
v_ref_741_ = lean_ctor_get(v___y_738_, 2);
v___x_742_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__0_spec__0(v_msg_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_751_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_751_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
lean_inc(v_ref_741_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v_ref_741_);
lean_ctor_set(v___x_747_, 1, v_a_743_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 1);
lean_ctor_set(v___x_745_, 0, v___x_747_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_735_ = stack[0].m_obj;
lean_object* v___y_736_ = stack[1].m_obj;
lean_object* v___y_737_ = stack[2].m_obj;
lean_object* v___y_738_ = stack[3].m_obj;
lean_object* v___y_739_ = stack[4].m_obj;
lean_object* v_res_752_;
v_res_752_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v_msg_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
stack->m_obj
 = v_res_752_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg___boxed(lean_object* v_msg_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v_msg_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_759_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__0));
v___x_762_ = l_Lean_stringToMessageData(v___x_761_);
return v___x_762_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(lean_object* v_x_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1, &l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___closed__1);
v___x_770_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v___x_769_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
return v___x_770_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_763_ = stack[0].m_obj;
lean_object* v___y_764_ = stack[1].m_obj;
lean_object* v___y_765_ = stack[2].m_obj;
lean_object* v___y_766_ = stack[3].m_obj;
lean_object* v___y_767_ = stack[4].m_obj;
lean_object* v_res_771_;
v_res_771_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(v_x_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
stack->m_obj
 = v_res_771_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0___boxed(lean_object* v_x_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__0(v_x_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v_x_772_);
return v_res_778_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(uint8_t v___x_782_, lean_object* v___f_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___y_794_; lean_object* v___x_806_; 
v___x_806_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_785_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_808_; uint8_t v___x_809_; uint8_t v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
v___x_808_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___closed__1));
v___x_809_ = 0;
v___x_810_ = 0;
v___x_811_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_811_, 0, v___x_809_);
lean_ctor_set_uint8(v___x_811_, 1, v___x_782_);
lean_ctor_set_uint8(v___x_811_, 2, v___x_810_);
lean_ctor_set_uint8(v___x_811_, 3, v___x_782_);
v___x_812_ = l_Lean_MVarId_applyConst(v_a_807_, v___x_808_, v___x_811_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
if (lean_obj_tag(v_a_813_) == 1)
{
lean_object* v_tail_814_; 
v_tail_814_ = lean_ctor_get(v_a_813_, 1);
if (lean_obj_tag(v_tail_814_) == 0)
{
lean_object* v_head_815_; lean_object* v___x_816_; 
lean_dec_ref(v___f_783_);
v_head_815_ = lean_ctor_get(v_a_813_, 0);
lean_inc(v_head_815_);
lean_dec_ref_known(v_a_813_, 2);
v___x_816_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_head_815_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
v___y_794_ = v___x_816_;
goto v___jp_793_;
}
else
{
lean_object* v___x_817_; 
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
v___x_817_ = lean_apply_6(v___f_783_, v_a_813_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, lean_box(0));
v___y_794_ = v___x_817_;
goto v___jp_793_;
}
}
else
{
lean_object* v___x_818_; 
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
v___x_818_ = lean_apply_6(v___f_783_, v_a_813_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, lean_box(0));
v___y_794_ = v___x_818_;
goto v___jp_793_;
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec_ref(v___f_783_);
v_a_819_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_812_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_812_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec_ref(v___f_783_);
v_a_827_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_806_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_806_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
v___jp_793_:
{
if (lean_obj_tag(v___y_794_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref_known(v___y_794_, 1);
v___x_795_ = lean_box(0);
v___x_796_ = lean_box(0);
v___x_797_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_795_, v___y_785_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v___x_797_, 0);
lean_dec(v_unused_805_);
v___x_799_ = v___x_797_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_dec(v___x_797_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_796_);
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_796_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
else
{
return v___x_797_;
}
}
else
{
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v___y_794_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_782_ = stack[0].m_num;
lean_object* v___f_783_ = stack[1].m_obj;
lean_object* v___y_784_ = stack[2].m_obj;
lean_object* v___y_785_ = stack[3].m_obj;
lean_object* v___y_786_ = stack[4].m_obj;
lean_object* v___y_787_ = stack[5].m_obj;
lean_object* v___y_788_ = stack[6].m_obj;
lean_object* v___y_789_ = stack[7].m_obj;
lean_object* v___y_790_ = stack[8].m_obj;
lean_object* v___y_791_ = stack[9].m_obj;
lean_object* v_res_835_;
v_res_835_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(v___x_782_, v___f_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed(lean_object* v___x_836_, lean_object* v___f_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
uint8_t v___x_1782__boxed_847_; lean_object* v_res_848_; 
v___x_1782__boxed_847_ = lean_unbox(v___x_836_);
v_res_848_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1(v___x_1782__boxed_847_, v___f_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_848_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__1));
v___x_853_ = l_Lean_MessageData_ofFormat(v___x_852_);
return v___x_853_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(lean_object* v___f_854_, lean_object* v_stx_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_865_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_862_);
v___x_866_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
v___x_867_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__2(v___x_865_, v___x_866_);
lean_dec_ref(v___x_865_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_854_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_obj_once(&l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2, &l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2_once, _init_l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___closed__2);
v___x_870_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Cbv_evalCbv_spec__3(v_stx_855_, v___x_869_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v___x_871_; 
lean_dec_ref_known(v___x_870_, 1);
v___x_871_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_854_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
return v___x_871_;
}
else
{
lean_dec_ref(v___f_854_);
return v___x_870_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_854_ = stack[0].m_obj;
lean_object* v_stx_855_ = stack[1].m_obj;
lean_object* v___y_856_ = stack[2].m_obj;
lean_object* v___y_857_ = stack[3].m_obj;
lean_object* v___y_858_ = stack[4].m_obj;
lean_object* v___y_859_ = stack[5].m_obj;
lean_object* v___y_860_ = stack[6].m_obj;
lean_object* v___y_861_ = stack[7].m_obj;
lean_object* v___y_862_ = stack[8].m_obj;
lean_object* v___y_863_ = stack[9].m_obj;
lean_object* v_res_872_;
v_res_872_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(v___f_854_, v_stx_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed(lean_object* v___f_873_, lean_object* v_stx_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2(v___f_873_, v_stx_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v_stx_874_);
return v_res_884_;
}
}
lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv(lean_object* v_stx_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1));
lean_inc(v_stx_892_);
v___x_903_ = l_Lean_Syntax_isOfKind(v_stx_892_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec(v_stx_892_);
v___x_904_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__1___redArg();
return v___x_904_;
}
else
{
lean_object* v___f_905_; lean_object* v___x_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___x_909_; 
v___f_905_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__2));
v___x_906_ = lean_box(v___x_903_);
v___f_907_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__1___boxed), 11, 2);
lean_closure_set(v___f_907_, 0, v___x_906_);
lean_closure_set(v___f_907_, 1, v___f_905_);
v___f_908_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___lam__2___boxed), 11, 2);
lean_closure_set(v___f_908_, 0, v___f_907_);
lean_closure_set(v___f_908_, 1, v_stx_892_);
v___x_909_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_908_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
return v___x_909_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Cbv_evalDecideCbv_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_892_ = stack[0].m_obj;
lean_object* v_a_893_ = stack[1].m_obj;
lean_object* v_a_894_ = stack[2].m_obj;
lean_object* v_a_895_ = stack[3].m_obj;
lean_object* v_a_896_ = stack[4].m_obj;
lean_object* v_a_897_ = stack[5].m_obj;
lean_object* v_a_898_ = stack[6].m_obj;
lean_object* v_a_899_ = stack[7].m_obj;
lean_object* v_a_900_ = stack[8].m_obj;
lean_object* v_res_910_;
v_res_910_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv(v_stx_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed(lean_object* v_stx_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Elab_Tactic_Cbv_evalDecideCbv(v_stx_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
return v_res_921_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(lean_object* v_00_u03b1_922_, lean_object* v_msg_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___redArg(v_msg_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
return v___x_929_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_923_ = stack[1].m_obj;
lean_object* v___y_924_ = stack[2].m_obj;
lean_object* v___y_925_ = stack[3].m_obj;
lean_object* v___y_926_ = stack[4].m_obj;
lean_object* v___y_927_ = stack[5].m_obj;
lean_object* v_res_930_;
v_res_930_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(lean_box(0), v_msg_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
stack->m_obj
 = v_res_930_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0___boxed(lean_object* v_00_u03b1_931_, lean_object* v_msg_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Cbv_evalDecideCbv_spec__0(v_00_u03b1_931_, v_msg_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_938_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1(){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_947_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_948_ = ((lean_object*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___closed__1));
v___x_949_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___closed__1));
v___x_950_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Cbv_evalDecideCbv___boxed), 10, 0);
v___x_951_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_947_, v___x_948_, v___x_949_, v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_952_;
v_res_952_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1___boxed(lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Elab_Tactic_Cbv_0__Lean_Elab_Tactic_Cbv_evalDecideCbv___regBuiltin_Lean_Elab_Tactic_Cbv_evalDecideCbv__1();
return v_res_954_;
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
